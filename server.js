import 'dotenv/config';
import express from 'express';
import Database from 'better-sqlite3';
import multer from 'multer';
import sharp from 'sharp';
import nodemailer from 'nodemailer';
import rateLimit from 'express-rate-limit';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const PORT = process.env.PORT || 3000;
const DATA = process.env.DATA_DIR || path.join(__dirname, 'data');
const UPLOADS = path.join(DATA, 'uploads');
fs.mkdirSync(UPLOADS, { recursive: true });

const prod = process.env.NODE_ENV === 'production';
const ADMINS = (process.env.ADMIN_EMAILS || '').toLowerCase().split(',').map(s => s.trim()).filter(Boolean);
const towns = (() => { try { return JSON.parse(fs.readFileSync(path.join(__dirname, 'towns.json'), 'utf8')); } catch { return {}; } })();
const scrypt = promisify(crypto.scrypt);

// ---------- database ----------
const db = new Database(path.join(DATA, 'app.db'));
db.pragma('journal_mode = WAL');
db.exec(`
CREATE TABLE IF NOT EXISTS users (
  id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL UNIQUE,
  salt TEXT NOT NULL, pw TEXT NOT NULL, town TEXT, created INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS sessions (
  token TEXT PRIMARY KEY, user_id INTEGER NOT NULL, expires INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS reports (
  id INTEGER PRIMARY KEY, user_id INTEGER NOT NULL, town TEXT NOT NULL, road TEXT, size TEXT,
  lat REAL NOT NULL, lng REAL NOT NULL, note TEXT, created INTEGER NOT NULL,
  filled_at INTEGER, filled_by INTEGER);
CREATE TABLE IF NOT EXISTS photos (
  hash TEXT PRIMARY KEY, bits TEXT NOT NULL, count INTEGER NOT NULL DEFAULT 1,
  report_id INTEGER, created INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS escalations (
  id INTEGER PRIMARY KEY, photo TEXT NOT NULL, count INTEGER NOT NULL,
  user_id INTEGER, created INTEGER NOT NULL);
`);

// ---------- helpers ----------
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const hashPw = async (pw, salt) => (await scrypt(pw, salt, 64)).toString('hex');
const cookies = req => Object.fromEntries((req.headers.cookie || '').split(';').map(s => s.trim().split('=')).filter(a => a[0]));
const isAdmin = u => !!u && ADMINS.includes(u.email);
const publicUser = u => ({ id: u.id, name: u.name, email: u.email, town: u.town, admin: isAdmin(u) });
const fail = (res, code, error) => res.status(code).json({ error });
const EMAIL = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;

function startSession(res, userId) {
  const token = crypto.randomBytes(32).toString('hex');
  const expires = Date.now() + 30 * 864e5;
  db.prepare('INSERT INTO sessions VALUES (?,?,?)').run(sha(token), userId, expires);
  res.cookie('pp_session', token, { httpOnly: true, sameSite: 'lax', secure: prod, maxAge: 30 * 864e5 });
}

async function normalize(buf) {
  return sharp(buf).rotate().resize(1400, 1400, { fit: 'inside', withoutEnlargement: true }).jpeg({ quality: 82 }).toBuffer();
}
async function dhash(jpg) {
  const px = await sharp(jpg).greyscale().resize(9, 8, { fit: 'fill' }).raw().toBuffer();
  let bits = '';
  for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++) bits += px[r * 9 + c] > px[r * 9 + c + 1] ? '1' : '0';
  return bits;
}
const hex = bits => bits.match(/.{4}/g).map(x => parseInt(x, 2).toString(16)).join('');
const ham = (a, b) => { let n = 0; for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) n++; return n; };

// AI screening with Google Gemini. Returns {checked:false} when no API key is set or the call fails.
const screenCache = new Map();
const PROMPT = 'You screen photos for a city road-repair app. Look at the image and reply with only JSON: {"pothole":boolean,"spam":boolean,"reason":"under 12 words"}. pothole is true if it shows a pothole or a damaged road surface. spam is true for screenshots, memes, selfies, stock or AI-made images, explicit or unrelated content, or anything that is clearly not a real photo of a road.';
async function screen(jpg) {
  const key = process.env.GEMINI_API_KEY;
  if (!key) return { checked: false };
  const id = sha(jpg.toString('base64'));
  if (screenCache.has(id)) return screenCache.get(id);
  try {
    const base = process.env.GEMINI_BASE || 'https://generativelanguage.googleapis.com';
    const model = process.env.GEMINI_MODEL || 'gemini-2.5-flash-lite';
    const r = await fetch(`${base}/v1beta/models/${model}:generateContent`, {
      method: 'POST',
      headers: { 'x-goog-api-key': key, 'content-type': 'application/json' },
      body: JSON.stringify({
        contents: [{ parts: [
          { inline_data: { mime_type: 'image/jpeg', data: jpg.toString('base64') } },
          { text: PROMPT }] }],
        generationConfig: { responseMimeType: 'application/json', maxOutputTokens: 300, temperature: 0 }
      })
    });
    const j = await r.json();
    if (j.promptFeedback?.blockReason) return { checked: true, pothole: false, spam: true, reason: 'blocked by safety filter' };
    const m = (j.candidates?.[0]?.content?.parts?.[0]?.text || '').match(/\{[\s\S]*\}/);
    if (!m) return { checked: false };
    const v = JSON.parse(m[0]);
    const out = { checked: true, pothole: !!v.pothole, spam: !!v.spam, reason: String(v.reason || '').slice(0, 120) };
    screenCache.set(id, out);
    if (screenCache.size > 500) screenCache.delete(screenCache.keys().next().value);
    return out;
  } catch { return { checked: false }; }
}

// Email (optional)
const mailer = process.env.SMTP_URL ? nodemailer.createTransport(process.env.SMTP_URL) : null;
async function sendMail(to, subject, text, jpg) {
  if (!mailer || !to) return false;
  try {
    await mailer.sendMail({
      from: process.env.MAIL_FROM || 'Pothole Patrol <no-reply@localhost>', to, subject, text,
      attachments: jpg ? [{ filename: 'pothole.jpg', content: jpg, contentType: 'image/jpeg' }] : []
    });
    return true;
  } catch (e) { console.error('mail failed:', e.message); return false; }
}

// ---------- app ----------
const app = express();
app.set('trust proxy', 1);
app.use(express.json({ limit: '50kb' }));
app.use(express.static(path.join(__dirname, 'public')));
const up = multer({ storage: multer.memoryStorage(), limits: { fileSize: 8 * 1024 * 1024, files: 1 } });
const authLimit = rateLimit({ windowMs: 15 * 60e3, limit: 30, standardHeaders: true, legacyHeaders: false });
const writeLimit = rateLimit({ windowMs: 60 * 60e3, limit: 60, standardHeaders: true, legacyHeaders: false });

app.use((req, _res, next) => {
  const t = cookies(req).pp_session;
  req.user = null;
  if (t) {
    const row = db.prepare('SELECT u.* FROM sessions s JOIN users u ON u.id = s.user_id WHERE s.token = ? AND s.expires > ?').get(sha(t), Date.now());
    if (row) req.user = row;
  }
  next();
});
const needUser = (req, res, next) => req.user ? next() : fail(res, 401, 'Please sign in.');
const needAdmin = (req, res, next) => isAdmin(req.user) ? next() : fail(res, 403, 'Admins only.');

app.post('/api/signup', authLimit, async (req, res) => {
  const { name = '', email = '', password = '', town = '' } = req.body || {};
  const em = String(email).trim().toLowerCase(), nm = String(name).trim();
  if (nm.length < 2 || nm.length > 60) return fail(res, 400, 'Enter your name.');
  if (!EMAIL.test(em) || em.length > 120) return fail(res, 400, 'Enter a valid email.');
  if (String(password).length < 8 || String(password).length > 200) return fail(res, 400, 'Password must be at least 8 characters.');
  if (db.prepare('SELECT 1 FROM users WHERE email = ?').get(em)) return fail(res, 409, 'That email already has an account. Sign in instead.');
  const salt = crypto.randomBytes(16).toString('hex');
  const id = db.prepare('INSERT INTO users (name,email,salt,pw,town,created) VALUES (?,?,?,?,?,?)')
    .run(nm, em, salt, await hashPw(password, salt), String(town).slice(0, 40), Date.now()).lastInsertRowid;
  startSession(res, id);
  res.json(publicUser(db.prepare('SELECT * FROM users WHERE id = ?').get(id)));
});

app.post('/api/login', authLimit, async (req, res) => {
  const em = String(req.body?.email || '').trim().toLowerCase(), pw = String(req.body?.password || '');
  const u = db.prepare('SELECT * FROM users WHERE email = ?').get(em);
  const ok = u && crypto.timingSafeEqual(Buffer.from(await hashPw(pw, u.salt), 'hex'), Buffer.from(u.pw, 'hex'));
  if (!ok) return fail(res, 401, 'Email or password is wrong.');
  startSession(res, u.id);
  res.json(publicUser(u));
});

app.post('/api/logout', (req, res) => {
  const t = cookies(req).pp_session;
  if (t) db.prepare('DELETE FROM sessions WHERE token = ?').run(sha(t));
  res.clearCookie('pp_session');
  res.json({ ok: true });
});

app.get('/api/me', needUser, (req, res) => res.json(publicUser(req.user)));

// Photo screening preview (shown while the person picks a size)
app.post('/api/check', needUser, writeLimit, up.single('photo'), async (req, res) => {
  if (!req.file) return fail(res, 400, 'Add a photo.');
  let jpg; try { jpg = await normalize(req.file.buffer); } catch { return fail(res, 400, 'That file isn’t a valid image.'); }
  res.json(await screen(jpg));
});

app.post('/api/reports', needUser, writeLimit, up.single('photo'), async (req, res) => {
  if (!req.file) return fail(res, 400, 'Add a photo.');
  const b = req.body, lat = parseFloat(b.lat), lng = parseFloat(b.lng);
  const town = String(b.town || '').slice(0, 40);
  if (!town) return fail(res, 400, 'Pick a town.');
  if (!isFinite(lat) || !isFinite(lng) || Math.abs(lat) > 90 || Math.abs(lng) > 180) return fail(res, 400, 'Add a valid location.');
  let jpg; try { jpg = await normalize(req.file.buffer); } catch { return fail(res, 400, 'That file isn’t a valid image.'); }

  const v = await screen(jpg);
  if (v.checked && (v.spam || !v.pothole)) return fail(res, 422, 'That photo doesn’t look like a pothole (' + (v.reason || 'unclear') + '). Retake it.');

  // Repeat detection: a photo within 8 bits of a stored fingerprint counts as the same photo.
  const bits = await dhash(jpg);
  const hit = db.prepare('SELECT * FROM photos').all().find(p => ham(p.bits, bits) <= 8);
  const size = ['Small', 'Medium', 'Large and dangerous'].includes(b.size) ? b.size : 'Medium';
  const road = b.road === 'state' ? 'state' : 'town';
  const note = String(b.note || '').slice(0, 500);
  const mapUrl = `https://www.google.com/maps?q=${lat},${lng}`;

  if (hit) {
    const count = hit.count + 1;
    db.prepare('UPDATE photos SET count = ? WHERE hash = ?').run(count, hit.hash);
    db.prepare('INSERT INTO escalations (photo,count,user_id,created) VALUES (?,?,?,?)').run(hit.hash, count, req.user.id, Date.now());
    await sendMail(process.env.ESCALATE_TO, `Repeat pothole photo (x${count}): ${town}, CT`,
      `The same photo has now been reported ${count} times.\nTown: ${town}\nLocation: ${mapUrl}\nLatest reporter: ${req.user.name} <${req.user.email}>`, jpg);
    return res.json({ repeat: count, emailed: false });
  }

  const id = db.prepare('INSERT INTO reports (user_id,town,road,size,lat,lng,note,created) VALUES (?,?,?,?,?,?,?,?)')
    .run(req.user.id, town, road, size, lat, lng, note, Date.now()).lastInsertRowid;
  db.prepare('INSERT INTO photos (hash,bits,count,report_id,created) VALUES (?,?,?,?,?)').run(hex(bits), bits, 1, id, Date.now());
  fs.writeFileSync(path.join(UPLOADS, id + '.jpg'), jpg);

  const to = road === 'town' ? towns[town]?.email : null;
  const emailed = await sendMail(to, `Pothole report: ${town}, CT (${lat.toFixed(5)}, ${lng.toFixed(5)})`,
    `Hello ${town} Public Works,\n\nA resident reported a pothole that needs repair.\n\nSize: ${size}\nCoordinates: ${lat}, ${lng}\nMap: ${mapUrl}\n${note ? 'Notes: ' + note + '\n' : ''}\nA photo is attached.\n\nReporter: ${req.user.name} <${req.user.email}>`, jpg);
  res.json({ id, repeat: 1, emailed });
});

app.get('/api/leaderboard', needUser, (req, res) => {
  const rows = db.prepare(`
    SELECT u.id, u.name, COUNT(r.id) AS submitted, COALESCE(SUM(r.filled_at IS NOT NULL), 0) AS filled
    FROM users u JOIN reports r ON r.user_id = u.id
    GROUP BY u.id ORDER BY filled DESC, submitted DESC, u.name LIMIT 50`).all();
  res.json(rows.map(r => ({ name: r.name, submitted: r.submitted, filled: r.filled, you: r.id === req.user.id })));
});

app.get('/api/admin/reports', needUser, needAdmin, (_req, res) => {
  res.json(db.prepare(`
    SELECT r.id, r.town, r.size, r.lat, r.lng, r.created, u.name
    FROM reports r JOIN users u ON u.id = r.user_id
    WHERE r.filled_at IS NULL ORDER BY r.created DESC LIMIT 100`).all());
});

app.post('/api/admin/reports/:id/fill', needUser, needAdmin, (req, res) => {
  const r = db.prepare('UPDATE reports SET filled_at = ?, filled_by = ? WHERE id = ? AND filled_at IS NULL')
    .run(Date.now(), req.user.id, Number(req.params.id));
  r.changes ? res.json({ ok: true }) : fail(res, 404, 'Already filled or not found.');
});

app.get('/api/photos/:id', needUser, (req, res) => {
  const id = Number(req.params.id);
  const r = db.prepare('SELECT user_id FROM reports WHERE id = ?').get(id);
  if (!r || (r.user_id !== req.user.id && !isAdmin(req.user))) return fail(res, 404, 'Not found.');
  res.sendFile(path.join(UPLOADS, id + '.jpg'));
});

app.use((err, _req, res, _next) => {
  if (err.code === 'LIMIT_FILE_SIZE') return fail(res, 413, 'That photo is too large (8 MB max).');
  console.error(err);
  fail(res, 500, 'Something went wrong.');
});

app.listen(PORT, () => console.log(`Pothole Patrol running on http://localhost:${PORT}`));
