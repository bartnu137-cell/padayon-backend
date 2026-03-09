/*
  Padayon Live Backend
  Phase 3:
  - Accounts with admin/editor/user roles
  - Session-based single-device login
  - Library storage + version history
  - PDF upload storage outside library.json
  - Score history + progress tracking
  - WebSocket presence + activity log
*/

const express = require('express');
const cors = require('cors');
const http = require('http');
const https = require('https');
const path = require('path');
const fs = require('fs');
const multer = require('multer');
const { WebSocketServer } = require('ws');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');

const PORT = Number(process.env.PORT || 3000);
const JWT_SECRET = String(process.env.JWT_SECRET || 'CHANGE_ME_IN_RENDER_ENV');
const RECAPTCHA_SECRET_KEY = String(process.env.RECAPTCHA_SECRET_KEY || '');
const CORS_ORIGIN_RAW = String(process.env.CORS_ORIGIN || '*');

const DATA_DIR = String(process.env.DATA_DIR || path.join(__dirname, 'data'));
const DB_FILE = path.join(DATA_DIR, 'db.json');
const INITIAL_LIBRARY_FILE = String(process.env.INITIAL_LIBRARY_FILE || path.join(__dirname, 'initial_library.json'));
const UPLOADS_DIR = path.join(DATA_DIR, 'uploads');
const PDF_UPLOADS_DIR = path.join(UPLOADS_DIR, 'pdfs');
const MAX_PDF_UPLOAD_MB = Number(process.env.MAX_PDF_UPLOAD_MB || 100);
const MAX_LIBRARY_VERSIONS = Number(process.env.MAX_LIBRARY_VERSIONS || 20);
const MAX_SCORE_HISTORY = Number(process.env.MAX_SCORE_HISTORY || 80);

function nowISO() {
  return new Date().toISOString();
}

function safeJsonParse(text, fallback = null) {
  try {
    return JSON.parse(text);
  } catch {
    return fallback;
  }
}

function ensureDir(dir) {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

function emptyLibrary() {
  return {
    version: 2,
    updatedAt: null,
    folders: [],
    quizSets: [],
    pdfs: [],
  };
}

function defaultDb() {
  return {
    accounts: [],
    library: emptyLibrary(),
    libraryVersions: [],
  };
}

function readJsonFileIfExists(filePath) {
  if (!fs.existsSync(filePath)) return null;
  const raw = fs.readFileSync(filePath, 'utf8');
  return safeJsonParse(raw, null);
}

function writeJsonAtomic(filePath, obj) {
  ensureDir(path.dirname(filePath));
  const tmp = filePath + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(obj, null, 2), 'utf8');
  fs.renameSync(tmp, filePath);
}

function normalizeUsername(u) {
  return String(u || '').trim();
}

function findAccount(db, username) {
  const u = normalizeUsername(username);
  if (!u) return null;
  return (db.accounts || []).find(a => String(a.username || '').toLowerCase() === u.toLowerCase()) || null;
}

function toSafeAccount(acc) {
  return {
    username: acc.username,
    role: acc.role,
    createdAt: acc.createdAt || null,
    lastLoginAt: acc.lastLoginAt || null,
  };
}

function ensureAccountCollections(acc) {
  if (!acc || typeof acc !== 'object') return acc;
  if (!Array.isArray(acc.scoreHistory)) acc.scoreHistory = [];
  if (!acc.progressBySet || typeof acc.progressBySet !== 'object' || Array.isArray(acc.progressBySet)) acc.progressBySet = {};
  return acc;
}

function clampInt(value, min, max, fallback = 0) {
  const n = Number(value);
  if (!Number.isFinite(n)) return fallback;
  return Math.min(max, Math.max(min, Math.round(n)));
}

function makeId(prefix) {
  return String(prefix || 'id') + '_' + Date.now().toString(36) + '_' + Math.random().toString(36).slice(2, 8);
}

function makeSessionId() {
  return 'sess_' + Date.now().toString(36) + '_' + Math.random().toString(36).slice(2, 10);
}

function safeFileStem(name) {
  return String(name || 'file')
    .replace(/\.[^.]+$/, '')
    .replace(/[^a-z0-9_-]+/gi, '_')
    .replace(/^_+|_+$/g, '')
    .slice(0, 80) || 'file';
}

function makeStoredPdfFilename(originalName) {
  const stem = safeFileStem(originalName);
  return `${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 8)}_${stem}.pdf`;
}

function getPublicBaseUrl(req) {
  const proto = String(req.headers['x-forwarded-proto'] || req.protocol || 'http').split(',')[0].trim();
  const host = String(req.get('host') || '').trim();
  return host ? `${proto}://${host}` : '';
}

function buildPdfUploadResponse(req, filename) {
  const relativePath = `/uploads/pdfs/${filename}`;
  const base = getPublicBaseUrl(req);
  return {
    filename,
    path: relativePath,
    url: base ? `${base}${relativePath}` : relativePath,
  };
}

function resolveManagedPdfPath(relativePath) {
  const clean = String(relativePath || '').trim();
  if (!clean.startsWith('/uploads/pdfs/')) return null;

  const filename = path.basename(clean);
  if (!filename || filename === '.' || filename === '..') return null;

  const abs = path.join(PDF_UPLOADS_DIR, filename);
  const normalizedRoot = path.resolve(PDF_UPLOADS_DIR) + path.sep;
  const normalizedAbs = path.resolve(abs);
  if (!normalizedAbs.startsWith(normalizedRoot)) return null;

  return { filename, abs: normalizedAbs, path: `/uploads/pdfs/${filename}` };
}

function sanitizeLibrary(input) {
  if (!input || typeof input !== 'object') return emptyLibrary();

  const version = Number(input.version || 0);
  if (version !== 2) {
    throw new Error('Library version must be 2.');
  }

  const out = emptyLibrary();
  out.version = 2;
  out.updatedAt = String(input.updatedAt || '') || null;
  out.folders = Array.isArray(input.folders) ? input.folders : [];
  out.quizSets = Array.isArray(input.quizSets) ? input.quizSets : [];

  const pdfs = Array.isArray(input.pdfs) ? input.pdfs : [];
  if (pdfs.some(p => String(p?.src || '').startsWith('data:'))) {
    throw new Error('Embedded PDF data URLs are no longer allowed. Store only PDF URLs/paths in library.');
  }
  out.pdfs = pdfs;
  return out;
}

function sanitizeScoreEntry(input) {
  const score = clampInt(input?.score, 0, 100000, 0);
  const total = clampInt(input?.total, 0, 100000, 0);
  const percent = total > 0 ? Math.round((score / total) * 1000) / 10 : 0;

  return {
    id: makeId('score'),
    ts: Date.now(),
    recordedAt: nowISO(),
    setId: String(input?.setId || '').slice(0, 120) || null,
    setTitle: String(input?.setTitle || 'Untitled Quiz').slice(0, 200),
    folder: String(input?.folder || '').slice(0, 240) || null,
    source: String(input?.source || 'custom').slice(0, 40) || 'custom',
    mode: String(input?.mode || 'exam').slice(0, 40) || 'exam',
    score,
    total,
    percent,
  };
}

function progressKeyFromEvent(event) {
  const setId = String(event?.setId || '').trim();
  if (setId) return setId;
  return `${String(event?.source || 'custom')}::${String(event?.folder || '')}::${String(event?.setTitle || 'Untitled Quiz')}`;
}

function sanitizeProgressEvent(input) {
  const score = clampInt(input?.score, 0, 100000, 0);
  const total = clampInt(input?.total, 0, 100000, 0);
  const percent = total > 0 ? Math.round((score / total) * 1000) / 10 : 0;
  return {
    id: makeId('prog'),
    ts: Date.now(),
    recordedAt: nowISO(),
    setId: String(input?.setId || '').slice(0, 120) || null,
    setTitle: String(input?.setTitle || 'Untitled Quiz').slice(0, 200),
    folder: String(input?.folder || '').slice(0, 240) || null,
    source: String(input?.source || 'custom').slice(0, 40) || 'custom',
    mode: String(input?.mode || 'study').slice(0, 40) || 'study',
    action: String(input?.action || 'view').slice(0, 40) || 'view',
    score,
    total,
    percent,
    correct: input?.correct === true,
  };
}

function applyProgressEvent(acc, event) {
  ensureAccountCollections(acc);
  const key = progressKeyFromEvent(event);
  const current = acc.progressBySet[key] || {
    key,
    setId: event.setId || null,
    setTitle: event.setTitle || 'Untitled Quiz',
    folder: event.folder || null,
    source: event.source || 'custom',
    practiceAttempts: 0,
    practiceCorrect: 0,
    examAttempts: 0,
    completedExams: 0,
    bestScore: 0,
    bestPercent: 0,
    lastScore: 0,
    lastPercent: 0,
    lastMode: event.mode || 'study',
    lastAction: event.action || 'view',
    firstSeenAt: event.recordedAt,
    lastEventAt: event.recordedAt,
  };

  current.setId = event.setId || current.setId || null;
  current.setTitle = event.setTitle || current.setTitle || 'Untitled Quiz';
  current.folder = event.folder || current.folder || null;
  current.source = event.source || current.source || 'custom';
  current.lastMode = event.mode || current.lastMode || 'study';
  current.lastAction = event.action || current.lastAction || 'view';
  current.lastEventAt = event.recordedAt || nowISO();

  if (event.action === 'practice_answer') {
    current.practiceAttempts += 1;
    if (event.correct) current.practiceCorrect += 1;
  }

  if (event.action === 'exam_submit' || event.action === 'random_exam_submit') {
    current.examAttempts += 1;
    current.completedExams += 1;
    current.lastScore = event.score;
    current.lastPercent = event.percent;
    if (event.percent >= current.bestPercent) {
      current.bestPercent = event.percent;
      current.bestScore = event.score;
    }
  }

  current.totalAttempts = current.practiceAttempts + current.examAttempts;
  acc.progressBySet[key] = current;
  return current;
}

function getProgressList(acc) {
  ensureAccountCollections(acc);
  return Object.values(acc.progressBySet || {}).sort((a, b) => {
    const aa = Date.parse(String(a.lastEventAt || '')) || 0;
    const bb = Date.parse(String(b.lastEventAt || '')) || 0;
    return bb - aa;
  });
}

function summarizeLibrary(lib) {
  const folders = Array.isArray(lib?.folders) ? lib.folders.length : 0;
  const quizSets = Array.isArray(lib?.quizSets) ? lib.quizSets.length : 0;
  const pdfs = Array.isArray(lib?.pdfs) ? lib.pdfs.length : 0;
  return { folders, quizSets, pdfs };
}

function createLibraryVersion(user, previousLibrary) {
  const snapshot = sanitizeLibrary(previousLibrary || emptyLibrary());
  return {
    id: makeId('ver'),
    ts: Date.now(),
    recordedAt: nowISO(),
    updatedBy: String(user?.username || 'system'),
    summary: summarizeLibrary(snapshot),
    library: snapshot,
  };
}

function verifyRecaptchaToken(token, remoteIp) {
  return new Promise((resolve) => {
    if (!RECAPTCHA_SECRET_KEY) {
      console.error('Missing RECAPTCHA_SECRET_KEY in environment.');
      return resolve(false);
    }

    const postData = new URLSearchParams({
      secret: RECAPTCHA_SECRET_KEY,
      response: String(token || ''),
    });

    if (remoteIp) postData.append('remoteip', String(remoteIp));

    const req = https.request(
      'https://www.google.com/recaptcha/api/siteverify',
      {
        method: 'POST',
        headers: {
          'Content-Type': 'application/x-www-form-urlencoded',
          'Content-Length': Buffer.byteLength(postData.toString()),
        },
      },
      (res) => {
        let body = '';
        res.on('data', (chunk) => { body += chunk; });
        res.on('end', () => {
          try {
            const json = JSON.parse(body);
            resolve(!!json.success);
          } catch (err) {
            console.error('reCAPTCHA parse error:', err);
            resolve(false);
          }
        });
      }
    );

    req.on('error', (err) => {
      console.error('reCAPTCHA request error:', err);
      resolve(false);
    });

    req.write(postData.toString());
    req.end();
  });
}

function initDbOnDisk() {
  ensureDir(DATA_DIR);
  ensureDir(UPLOADS_DIR);
  ensureDir(PDF_UPLOADS_DIR);

  let db = readJsonFileIfExists(DB_FILE);
  if (!db || typeof db !== 'object') db = defaultDb();

  if (!db.library || typeof db.library !== 'object' || Number(db.library.version || 0) !== 2) {
    const initial = readJsonFileIfExists(INITIAL_LIBRARY_FILE);
    if (initial && typeof initial === 'object') {
      try {
        db.library = sanitizeLibrary(initial);
      } catch {
        db.library = emptyLibrary();
      }
    } else {
      db.library = emptyLibrary();
    }
  }

  if (!Array.isArray(db.accounts)) db.accounts = [];
  if (!Array.isArray(db.libraryVersions)) db.libraryVersions = [];

  let changed = false;
  const wantSeed = [
    { username: 'admin', password: 'admin', role: 'admin' },
    { username: 'saligao', password: 'carl', role: 'user' },
    { username: 'ramos', password: 'carl', role: 'user' },
    { username: 'fernandez', password: 'cristopher', role: 'user' },
    { username: 'cortez', password: 'cyron', role: 'user' },
    { username: 'castillo', password: 'gian', role: 'user' },
    { username: 'maceda', password: 'mj', role: 'user' },
    { username: 'quillopo', password: 'pj', role: 'user' },
    { username: 'arcenas', password: 'rheygie', role: 'user' },
    { username: 'felizarta', password: 'treb', role: 'user' },
  ];

  wantSeed.forEach(seed => {
    if (!findAccount(db, seed.username)) {
      db.accounts.push({
        username: seed.username,
        passwordHash: bcrypt.hashSync(seed.password, 10),
        role: seed.role,
        createdAt: nowISO(),
        scoreHistory: [],
        progressBySet: {},
      });
      changed = true;
    }
  });

  db.accounts.forEach(acc => {
    ensureAccountCollections(acc);
    if (!['admin', 'editor', 'user'].includes(String(acc.role || 'user'))) {
      acc.role = 'user';
      changed = true;
    }
  });

  if (changed || !fs.existsSync(DB_FILE)) {
    writeJsonAtomic(DB_FILE, db);
  }

  return db;
}

let db = initDbOnDisk();

function saveDb() {
  writeJsonAtomic(DB_FILE, db);
}

function parseAllowedOrigins(raw) {
  const r = String(raw || '').trim();
  if (!r || r === '*') return { any: true, list: [] };
  const list = r.split(',').map(s => s.trim()).filter(Boolean);
  return { any: false, list };
}

const allowedOrigins = parseAllowedOrigins(CORS_ORIGIN_RAW);

function isOriginAllowed(origin) {
  if (allowedOrigins.any) return true;
  if (!origin) return true;
  return allowedOrigins.list.includes(origin);
}

function getUserFromActiveToken(token) {
  try {
    const decoded = jwt.verify(String(token || ''), JWT_SECRET);
    const acc = findAccount(db, decoded.username);
    if (!acc) return null;
    if (!decoded.sessionId) return null;
    if (acc.sessionId !== decoded.sessionId) return null;
    return {
      username: acc.username,
      role: acc.role,
      sessionId: acc.sessionId,
    };
  } catch {
    return null;
  }
}

const app = express();
app.use(express.json({ limit: '25mb' }));
app.use(cors({
  origin: (origin, cb) => {
    if (isOriginAllowed(origin)) return cb(null, true);
    return cb(new Error('CORS blocked for origin: ' + origin));
  },
  methods: ['GET', 'POST', 'PUT', 'DELETE', 'OPTIONS'],
  allowedHeaders: ['Content-Type', 'Authorization'],
}));
app.use('/uploads', express.static(UPLOADS_DIR, {
  maxAge: '7d',
  index: false,
}));

const pdfUpload = multer({
  storage: multer.diskStorage({
    destination: (_req, _file, cb) => {
      ensureDir(PDF_UPLOADS_DIR);
      cb(null, PDF_UPLOADS_DIR);
    },
    filename: (_req, file, cb) => {
      cb(null, makeStoredPdfFilename(file.originalname || 'file.pdf'));
    },
  }),
  limits: {
    fileSize: MAX_PDF_UPLOAD_MB * 1024 * 1024,
  },
  fileFilter: (_req, file, cb) => {
    const mime = String(file.mimetype || '').toLowerCase();
    const ext = path.extname(String(file.originalname || '')).toLowerCase();
    if (mime === 'application/pdf' || ext === '.pdf') return cb(null, true);
    return cb(new Error('Only PDF files are allowed.'));
  },
});

function requireAuth(req, res, next) {
  const hdr = String(req.headers.authorization || '');
  const token = hdr.startsWith('Bearer ') ? hdr.slice('Bearer '.length) : '';
  if (!token) return res.status(401).json({ error: 'Missing Bearer token.' });

  const user = getUserFromActiveToken(token);
  if (!user) return res.status(401).json({ error: 'Invalid or expired session.' });

  req.user = user;
  return next();
}

function requireAdmin(req, res, next) {
  if (!req.user) return res.status(401).json({ error: 'Unauthorized.' });
  if (req.user.role !== 'admin') return res.status(403).json({ error: 'Admin only.' });
  return next();
}

function requireContentManager(req, res, next) {
  if (!req.user) return res.status(401).json({ error: 'Unauthorized.' });
  if (!['admin', 'editor'].includes(String(req.user.role || ''))) {
    return res.status(403).json({ error: 'Admin or editor only.' });
  }
  return next();
}

app.get('/', (_req, res) => {
  res.type('text/plain').send('Padayon Live Backend is running.');
});

app.get('/api/health', (_req, res) => {
  res.json({ ok: true, time: nowISO() });
});

app.post('/api/auth/login', async (req, res) => {
  const username = normalizeUsername(req.body?.username);
  const password = String(req.body?.password || '');
  const captchaToken = String(req.body?.captchaToken || '');

  if (!username || !password) {
    return res.status(400).json({ error: 'username and password required.' });
  }
  if (!captchaToken) {
    return res.status(400).json({ error: 'Please complete the captcha.' });
  }

  const captchaOk = await verifyRecaptchaToken(captchaToken, req.ip);
  if (!captchaOk) {
    return res.status(400).json({ error: 'Captcha verification failed.' });
  }

  const acc = findAccount(db, username);
  if (!acc) return res.status(401).json({ error: 'Invalid credentials.' });

  const ok = bcrypt.compareSync(password, acc.passwordHash || '');
  if (!ok) return res.status(401).json({ error: 'Invalid credentials.' });

  acc.sessionId = makeSessionId();
  acc.lastLoginAt = nowISO();
  ensureAccountCollections(acc);
  saveDb();

  forceLogoutUserSockets(acc.username);

  const token = jwt.sign(
    {
      username: acc.username,
      role: acc.role,
      sessionId: acc.sessionId,
    },
    JWT_SECRET,
    { expiresIn: '30d' }
  );

  return res.json({
    token,
    user: { username: acc.username, role: acc.role },
  });
});

app.post('/api/uploads/pdf', requireAuth, requireContentManager, (req, res) => {
  pdfUpload.single('file')(req, res, (err) => {
    if (err) {
      const message = err instanceof multer.MulterError
        ? (err.code === 'LIMIT_FILE_SIZE' ? `PDF is too large. Max size is ${MAX_PDF_UPLOAD_MB} MB.` : err.message)
        : String(err?.message || err);
      return res.status(400).json({ error: message });
    }

    if (!req.file) {
      return res.status(400).json({ error: 'PDF file is required.' });
    }

    const fileInfo = buildPdfUploadResponse(req, req.file.filename);
    addLog(req.user.username, `Uploaded PDF: ${req.file.originalname || req.file.filename}`);
    return res.json({ ok: true, file: fileInfo });
  });
});

app.delete('/api/uploads/pdf', requireAuth, requireContentManager, (req, res) => {
  const resolved = resolveManagedPdfPath(req.body?.path || '');
  if (!resolved) return res.status(400).json({ error: 'Invalid PDF path.' });

  try {
    if (fs.existsSync(resolved.abs)) fs.unlinkSync(resolved.abs);
    addLog(req.user.username, `Deleted PDF: ${resolved.filename}`);
    return res.json({ ok: true });
  } catch (err) {
    return res.status(500).json({ error: String(err?.message || err) });
  }
});

app.get('/api/library', (_req, res) => {
  res.json(db.library || emptyLibrary());
});

app.get('/api/library/versions', requireAuth, requireContentManager, (_req, res) => {
  const items = Array.isArray(db.libraryVersions) ? db.libraryVersions.map(v => ({
    id: v.id,
    ts: v.ts,
    recordedAt: v.recordedAt,
    updatedBy: v.updatedBy,
    summary: v.summary || summarizeLibrary(v.library),
  })) : [];
  res.json({ items });
});

app.post('/api/library/restore/:id', requireAuth, requireAdmin, (req, res) => {
  const id = String(req.params.id || '').trim();
  const item = (db.libraryVersions || []).find(v => String(v.id) === id);
  if (!item) return res.status(404).json({ error: 'Version not found.' });

  try {
    const restored = sanitizeLibrary(item.library || emptyLibrary());
    restored.updatedAt = nowISO();

    const previous = sanitizeLibrary(db.library || emptyLibrary());
    const snapshot = createLibraryVersion(req.user, previous);
    db.libraryVersions.unshift(snapshot);
    db.libraryVersions = db.libraryVersions.slice(0, MAX_LIBRARY_VERSIONS);

    db.library = restored;
    saveDb();

    const ms = Date.parse(restored.updatedAt) || Date.now();
    broadcastAll({ type: 'library:changed', ms, updatedAt: restored.updatedAt });
    addLog(req.user.username, `Restored library version: ${id}`);
    return res.json({ ok: true, updatedAt: restored.updatedAt });
  } catch (err) {
    return res.status(400).json({ error: String(err?.message || err) });
  }
});

app.put('/api/library', requireAuth, requireContentManager, (req, res) => {
  try {
    const previous = sanitizeLibrary(db.library || emptyLibrary());
    const incoming = sanitizeLibrary(req.body);
    incoming.updatedAt = nowISO();

    const snapshot = createLibraryVersion(req.user, previous);
    db.libraryVersions.unshift(snapshot);
    db.libraryVersions = db.libraryVersions.slice(0, MAX_LIBRARY_VERSIONS);

    db.library = incoming;
    saveDb();

    const ms = Date.parse(incoming.updatedAt) || Date.now();
    broadcastAll({ type: 'library:changed', ms, updatedAt: incoming.updatedAt });
    addLog(req.user.username, 'Library updated');
    return res.json({ ok: true, updatedAt: incoming.updatedAt });
  } catch (err) {
    return res.status(400).json({ error: String(err?.message || err) });
  }
});

app.get('/api/accounts', requireAuth, requireAdmin, (_req, res) => {
  const accounts = (db.accounts || []).map(toSafeAccount);
  res.json({ accounts });
});

app.post('/api/accounts', requireAuth, requireAdmin, (req, res) => {
  const username = normalizeUsername(req.body?.username);
  const password = String(req.body?.password || '');
  const rawRole = String(req.body?.role || 'user').toLowerCase();
  const role = ['admin', 'editor', 'user'].includes(rawRole) ? rawRole : 'user';

  if (!username || !password) return res.status(400).json({ error: 'username and password required.' });
  if (password.length < 3) return res.status(400).json({ error: 'password too short.' });
  if (findAccount(db, username)) return res.status(409).json({ error: 'Account already exists.' });

  const acc = {
    username,
    passwordHash: bcrypt.hashSync(password, 10),
    role,
    createdAt: nowISO(),
    scoreHistory: [],
    progressBySet: {},
  };

  db.accounts.push(acc);
  saveDb();

  addLog(req.user.username, `Created account: ${username} (${role})`);
  return res.json({ ok: true, account: toSafeAccount(acc) });
});

app.get('/api/scores', requireAuth, (req, res) => {
  const acc = findAccount(db, req.user.username);
  if (!acc) return res.status(404).json({ error: 'Account not found.' });
  ensureAccountCollections(acc);
  return res.json({ items: acc.scoreHistory.slice().sort((a, b) => Number(b.ts || 0) - Number(a.ts || 0)) });
});

app.post('/api/scores', requireAuth, (req, res) => {
  const acc = findAccount(db, req.user.username);
  if (!acc) return res.status(404).json({ error: 'Account not found.' });
  ensureAccountCollections(acc);

  const item = sanitizeScoreEntry(req.body || {});
  acc.scoreHistory.unshift(item);
  acc.scoreHistory = acc.scoreHistory.slice(0, MAX_SCORE_HISTORY);
  saveDb();
  addLog(req.user.username, `Saved score: ${item.setTitle} ${item.score}/${item.total}`);
  return res.json({ ok: true, item });
});

app.get('/api/progress', requireAuth, (req, res) => {
  const acc = findAccount(db, req.user.username);
  if (!acc) return res.status(404).json({ error: 'Account not found.' });
  return res.json({ items: getProgressList(acc) });
});

app.post('/api/progress', requireAuth, (req, res) => {
  const acc = findAccount(db, req.user.username);
  if (!acc) return res.status(404).json({ error: 'Account not found.' });
  const event = sanitizeProgressEvent(req.body || {});
  const item = applyProgressEvent(acc, event);
  saveDb();
  return res.json({ ok: true, item });
});

let forceLogoutUserSockets = () => {};
const server = http.createServer(app);
const wss = new WebSocketServer({ server, path: '/ws' });

const clients = new Map();
let activityLog = [];

function wsSend(ws, obj) {
  try {
    if (ws.readyState === ws.OPEN) ws.send(JSON.stringify(obj));
  } catch {
    // ignore
  }
}

function addLog(username, message) {
  const item = { ts: Date.now(), username: String(username || ''), message: String(message || '') };
  activityLog.push(item);
  if (activityLog.length > 300) activityLog = activityLog.slice(-300);
  broadcastAdmins({ type: 'log:append', item });
}

function getOnlineStates() {
  return Array.from(clients.values())
    .filter(s => s && s.username)
    .map(s => ({
      username: s.username,
      role: s.role,
      activity: s.activity,
      view: s.view,
      path: s.path,
      details: s.details,
      clientId: s.clientId,
      connectedAt: s.connectedAt,
      lastSeen: s.lastSeen,
    }));
}

function presencePayloadPublic() {
  return { type: 'presence:public', users: getOnlineStates().map(u => ({ username: u.username, role: u.role })) };
}

function presencePayloadAdmin() {
  return { type: 'presence:admin', users: getOnlineStates() };
}

function broadcastAll(obj) {
  wss.clients.forEach(ws => wsSend(ws, obj));
}

function broadcastAdmins(obj) {
  wss.clients.forEach(ws => {
    const st = clients.get(ws);
    if (st && st.role === 'admin') wsSend(ws, obj);
  });
}

let presenceTimer = null;
function schedulePresenceBroadcast() {
  if (presenceTimer) return;
  presenceTimer = setTimeout(() => {
    presenceTimer = null;
    const pub = presencePayloadPublic();
    const adm = presencePayloadAdmin();
    wss.clients.forEach(ws => {
      const st = clients.get(ws);
      if (!st || !st.authed) return;
      wsSend(ws, st.role === 'admin' ? adm : pub);
    });
  }, 200);
}

function summarizeActivity(msg) {
  const a = String(msg?.activity || '').trim();
  const view = String(msg?.view || '').trim();
  const path0 = String(msg?.path || '').trim();
  const details = msg?.details;
  const d = (details === null || details === undefined) ? '' : String(details).trim();
  const bits = [];
  if (a) bits.push(a);
  if (d) bits.push('— ' + d);
  if (path0) bits.push('(' + path0 + ')');
  if (view) bits.push('[' + view + ']');
  return bits.join(' ');
}

forceLogoutUserSockets = function (username) {
  const target = String(username || '').toLowerCase();
  wss.clients.forEach(ws => {
    const st = clients.get(ws);
    if (!st || !st.username) return;
    if (String(st.username).toLowerCase() === target) {
      wsSend(ws, { type: 'force_logout', reason: 'This account was logged in on another device.' });
      try { ws.close(); } catch {}
    }
  });
};

wss.on('connection', (ws, req) => {
  const origin = req.headers.origin;
  if (!isOriginAllowed(origin)) {
    try { ws.close(); } catch {}
    return;
  }

  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });

  const state = {
    authed: false,
    username: '',
    role: 'user',
    clientId: null,
    activity: 'Online',
    view: 'LOGIN',
    path: null,
    details: null,
    connectedAt: Date.now(),
    lastSeen: Date.now(),
    _lastLogKey: '',
    _lastLogTs: 0,
  };
  clients.set(ws, state);

  const helloTimeout = setTimeout(() => {
    const st = clients.get(ws);
    if (st && !st.authed) {
      try { ws.close(); } catch {}
    }
  }, 8000);

  ws.on('message', (data) => {
    const raw = Buffer.isBuffer(data) ? data.toString('utf8') : String(data || '');
    const msg = safeJsonParse(raw, null);
    if (!msg || typeof msg !== 'object') return;

    const st = clients.get(ws);
    if (!st) return;
    const type = String(msg.type || '');

    if (type === 'hello') {
      const tokenUser = getUserFromActiveToken(msg?.token);
      if (!tokenUser) {
        wsSend(ws, { type: 'error', error: 'hello requires a valid token' });
        try { ws.close(); } catch {}
        return;
      }

      st.authed = true;
      st.username = tokenUser.username;
      st.role = tokenUser.role;
      st.clientId = String(msg.clientId || '') || null;
      st.lastSeen = Date.now();
      clearTimeout(helloTimeout);

      wsSend(ws, {
        type: 'hello:ack',
        user: { username: st.username, role: st.role },
        serverTime: Date.now(),
      });

      wsSend(ws, st.role === 'admin' ? presencePayloadAdmin() : presencePayloadPublic());
      if (st.role === 'admin') wsSend(ws, { type: 'log:batch', items: activityLog.slice(-200) });

      addLog(st.username, 'Connected');
      schedulePresenceBroadcast();
      return;
    }

    if (!st.authed) return;

    if (type === 'activity') {
      st.lastSeen = Date.now();
      st.activity = String(msg.activity || st.activity || 'Online').slice(0, 180);
      st.view = String(msg.view || st.view || 'UNKNOWN').slice(0, 80);
      st.path = (msg.path === null || msg.path === undefined) ? null : String(msg.path).slice(0, 240);
      st.details = (msg.details === null || msg.details === undefined) ? null : String(msg.details).slice(0, 240);

      schedulePresenceBroadcast();

      const key = `${st.activity}|${st.view}|${st.path || ''}|${st.details || ''}`;
      const now = Date.now();
      if (key !== st._lastLogKey || (now - st._lastLogTs) > 2500) {
        st._lastLogKey = key;
        st._lastLogTs = now;
        addLog(st.username, summarizeActivity({
          activity: st.activity,
          view: st.view,
          path: st.path,
          details: st.details,
        }));
      }
      return;
    }

    if (type === 'presence:request') {
      wsSend(ws, st.role === 'admin' ? presencePayloadAdmin() : presencePayloadPublic());
      return;
    }

    if (type === 'log:request') {
      if (st.role === 'admin') wsSend(ws, { type: 'log:batch', items: activityLog.slice(-200) });
    }
  });

  ws.on('close', () => {
    clearTimeout(helloTimeout);
    const st = clients.get(ws);
    clients.delete(ws);
    if (st && st.authed && st.username) {
      addLog(st.username, 'Disconnected');
      schedulePresenceBroadcast();
    }
  });
});

setInterval(() => {
  wss.clients.forEach(ws => {
    if (ws.isAlive === false) {
      try { ws.terminate(); } catch {}
      return;
    }
    ws.isAlive = false;
    try { ws.ping(); } catch {}
  });
}, 30000);

server.listen(PORT, () => {
  console.log(`Padayon backend listening on :${PORT}`);
  console.log(`CORS origin: ${CORS_ORIGIN_RAW}`);
  console.log(`DB file: ${DB_FILE}`);
});
