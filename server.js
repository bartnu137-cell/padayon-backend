/*
  Padayon Live Backend
  - Accounts (admin can create)
  - Library storage (admin edits push here)
  - WebSocket presence (online users) + activity tracking + live library update events

  Designed for Render Web Services.
*/

const express = require('express');
const cors = require('cors');
const http = require('http');
const https = require('https');
const path = require('path');
const fs = require('fs');
const { WebSocketServer } = require('ws');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');

const PORT = Number(process.env.PORT || 3000);
const JWT_SECRET = String(process.env.JWT_SECRET || 'CHANGE_ME_IN_RENDER_ENV');
const RECAPTCHA_SECRET_KEY = String(process.env.RECAPTCHA_SECRET_KEY || '');
const CORS_ORIGIN_RAW = String(process.env.CORS_ORIGIN || '*');


// If you attach a Render Disk, set DATA_DIR=/var/data (or whatever mount path you pick)
const DATA_DIR = String(process.env.DATA_DIR || path.join(__dirname, 'data'));
const DB_FILE = path.join(DATA_DIR, 'db.json');

// Used only when db.json doesn't exist yet
const INITIAL_LIBRARY_FILE = String(process.env.INITIAL_LIBRARY_FILE || path.join(__dirname, 'initial_library.json'));

function nowISO() {
  return new Date().toISOString();
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

    if (remoteIp) {
      postData.append('remoteip', String(remoteIp));
    }

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

        res.on('data', (chunk) => {
          body += chunk;
        });

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
  return db.accounts.find(a => String(a.username).toLowerCase() === u.toLowerCase()) || null;
}

function toSafeAccount(acc) {
  return {
    username: acc.username,
    role: acc.role,
    createdAt: acc.createdAt || null,
  };
}

function sanitizeLibrary(input) {
  if (!input || typeof input !== 'object') return emptyLibrary();

  // Require version 2 for compatibility
  const version = Number(input.version || 0);
  if (version !== 2) {
    throw new Error('Library version must be 2.');
  }

  const out = emptyLibrary();
  out.version = 2;
  out.updatedAt = String(input.updatedAt || '') || null;
  out.folders = Array.isArray(input.folders) ? input.folders : [];
  out.quizSets = Array.isArray(input.quizSets) ? input.quizSets : [];
  out.pdfs = Array.isArray(input.pdfs) ? input.pdfs : [];

  return out;
}

function initDbOnDisk() {
  ensureDir(DATA_DIR);

  let db = readJsonFileIfExists(DB_FILE);
  if (!db || typeof db !== 'object') db = defaultDb();

  // If no library exists yet, try bootstrap from initial_library.json
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

  // Ensure at least one admin exists.
  // These match your existing frontend defaults.
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
      });
      changed = true;
    }
  });

  if (!Array.isArray(db.accounts)) {
    db.accounts = [];
    changed = true;
  }

  if (changed || !fs.existsSync(DB_FILE)) {
    writeJsonAtomic(DB_FILE, db);
  }

  return db;
}

let db = initDbOnDisk();

function saveDb() {
  writeJsonAtomic(DB_FILE, db);
}

// --- CORS ---
function parseAllowedOrigins(raw) {
  const r = String(raw || '').trim();
  if (!r || r === '*') return { any: true, list: [] };
  const list = r.split(',').map(s => s.trim()).filter(Boolean);
  return { any: false, list };
}

const allowedOrigins = parseAllowedOrigins(CORS_ORIGIN_RAW);

function isOriginAllowed(origin) {
  if (allowedOrigins.any) return true;
  if (!origin) return true; // non-browser / server-to-server
  return allowedOrigins.list.includes(origin);
}

const app = express();
app.use(express.json({ limit: '200mb' }));
app.use(cors({
  origin: (origin, cb) => {
    if (isOriginAllowed(origin)) return cb(null, true);
    return cb(new Error('CORS blocked for origin: ' + origin));
  },
  methods: ['GET', 'POST', 'PUT', 'OPTIONS'],
  allowedHeaders: ['Content-Type', 'Authorization'],
}));

// --- Auth middleware ---
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

// --- API ---
app.get('/', (req, res) => {
  res.type('text/plain').send('Padayon Live Backend is running.');
});

app.get('/api/health', (req, res) => {
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

app.get('/api/library', (req, res) => {
  res.json(db.library || emptyLibrary());
});


app.put('/api/library', requireAuth, requireAdmin, (req, res) => {
  try {
    const incoming = sanitizeLibrary(req.body);
    // Server is source of truth for updatedAt
    incoming.updatedAt = nowISO();

    db.library = incoming;
    saveDb();

    const ms = Date.parse(incoming.updatedAt) || Date.now();
    broadcastAll({ type: 'library:changed', ms, updatedAt: incoming.updatedAt });
    addLog(req.user.username, 'Library updated');

    res.json({ ok: true, updatedAt: incoming.updatedAt });
  } catch (err) {
    res.status(400).json({ error: String(err?.message || err) });
  }
});

app.get('/api/accounts', requireAuth, requireAdmin, (req, res) => {
  const accounts = (db.accounts || []).map(toSafeAccount);
  res.json({ accounts });
});

app.post('/api/accounts', requireAuth, requireAdmin, (req, res) => {
  const username = normalizeUsername(req.body?.username);
  const password = String(req.body?.password || '');
  const role = (String(req.body?.role || 'user') === 'admin') ? 'admin' : 'user';

  if (!username || !password) return res.status(400).json({ error: 'username and password required.' });
  if (password.length < 3) return res.status(400).json({ error: 'password too short.' });

  if (findAccount(db, username)) return res.status(409).json({ error: 'Account already exists.' });

  const acc = {
    username,
    passwordHash: bcrypt.hashSync(password, 10),
    role,
    createdAt: nowISO(),
  };

  db.accounts.push(acc);
  saveDb();

  addLog(req.user.username, `Created account: ${username} (${role})`);

  res.json({ ok: true, account: toSafeAccount(acc) });
});

// --- WebSockets ---
let forceLogoutUserSockets = () => {};

const server = http.createServer(app);
const wss = new WebSocketServer({ server, path: '/ws' });

forceLogoutUserSockets = function (username) {
  const target = String(username || '').toLowerCase();

  wss.clients.forEach(ws => {
    const st = clients.get(ws);
    if (!st || !st.username) return;

    if (String(st.username).toLowerCase() === target) {
      wsSend(ws, {
        type: 'force_logout',
        reason: 'This account was logged in on another device.',
      });

      try { ws.close(); } catch {}
    }
  });
};

// ws -> state
const clients = new Map();

let activityLog = []; // { ts, username, message }

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
  const users = getOnlineStates().map(u => ({ username: u.username, role: u.role }));
  return { type: 'presence:public', users };
}

function presencePayloadAdmin() {
  return { type: 'presence:admin', users: getOnlineStates() };
}

function wsSend(ws, obj) {
  try {
    if (ws.readyState === ws.OPEN) ws.send(JSON.stringify(obj));
  } catch {
    // ignore
  }
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

function userFromToken(token) {
  return getUserFromActiveToken(token);
}

function safeHelloUser(msg) {
  const tok = msg?.token;
  if (!tok) return null;

  const u = userFromToken(tok);
  if (!u) return null;

  return u;
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

wss.on('connection', (ws, req) => {
  // Origin guard (optional)
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
    const raw = (Buffer.isBuffer(data) ? data.toString('utf8') : String(data || ''));
    const msg = safeJsonParse(raw, null);
    if (!msg || typeof msg !== 'object') return;

    const st = clients.get(ws);
    if (!st) return;

    const type = String(msg.type || '');

    if (type === 'hello') {
      const u = safeHelloUser(msg);
      if (!u) {
        wsSend(ws, { type: 'error', error: 'hello requires a valid token' });
        try { ws.close(); } catch {}
        return;
      }

      st.authed = true;
      st.username = u.username;
      st.role = u.role;
      st.clientId = String(msg.clientId || '') || null;
      st.lastSeen = Date.now();

      clearTimeout(helloTimeout);

      wsSend(ws, {
        type: 'hello:ack',
        user: { username: st.username, role: st.role },
        serverTime: Date.now(),
      });

      // Send initial snapshots
      wsSend(ws, st.role === 'admin' ? presencePayloadAdmin() : presencePayloadPublic());
      if (st.role === 'admin') {
        wsSend(ws, { type: 'log:batch', items: activityLog.slice(-200) });
      }

      addLog(st.username, 'Connected');
      schedulePresenceBroadcast();
      return;
    }

    // Ignore everything until hello
    if (!st.authed) return;

    if (type === 'activity') {
      st.lastSeen = Date.now();
      st.activity = String(msg.activity || st.activity || 'Online').slice(0, 180);
      st.view = String(msg.view || st.view || 'UNKNOWN').slice(0, 80);
      st.path = (msg.path === null || msg.path === undefined) ? null : String(msg.path).slice(0, 240);
      st.details = (msg.details === null || msg.details === undefined) ? null : String(msg.details).slice(0, 240);

      schedulePresenceBroadcast();

      // Rate-limited logging
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
      return;
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

// Heartbeat
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

function makeSessionId() {
  return 'sess_' + Date.now().toString(36) + '_' + Math.random().toString(36).slice(2, 10);
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
