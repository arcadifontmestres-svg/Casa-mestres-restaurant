'use strict';
const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { exec } = require('child_process');
const { handleMcpRequest } = require('./mcp.js');
const { authenticateBearer, handleOAuthRequest, oauthChallenge } = require('./oauth.js');
const { createCriterion, updateCriterion, transitionCriterion } = require('./criteria.js');

const ROOT = __dirname;
const PUBLIC = path.join(ROOT, 'public');
const SEED_DATA = path.join(ROOT, 'data.json');
// ── CORRECCIÓ: noms reals dels fitxers seed al repositori ─────────────────────
const CATALOG_DATA     = path.join(ROOT, 'seed', 'catàleg.json');
const SARRIERA_DATA    = path.join(ROOT, 'seed', 'sarrera-kitchen-bases.json');
const DISH_RECIPE_DATA = path.join(ROOT, 'seed', 'propostes-de-receptes-de-plats.json');

function loadEnv() {
  const file = path.join(ROOT, '.env');
  if (!fs.existsSync(file)) return;
  for (const line of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
    const text = line.trim();
    if (!text || text.startsWith('#')) continue;
    const separator = text.indexOf('=');
    if (separator < 1) continue;
    const key = text.slice(0, separator).trim();
    const value = text.slice(separator + 1).trim();
    if (!process.env[key]) process.env[key] = value;
  }
}

loadEnv();

const configuredDataDir = String(process.env.DATA_DIR || '').trim();
const DATA_DIR = configuredDataDir ? path.resolve(configuredDataDir) : ROOT;
const DATA = path.join(DATA_DIR, 'data.json');
const BACKUPS = path.join(DATA_DIR, 'backups');
const PORT = Number(process.env.PORT || 3210);
const HOST = process.env.HOST || '0.0.0.0';
const stripeTestSessions = new Map();
const deviceActivationAttempts = new Map();

function ensureStorage() {
  fs.mkdirSync(DATA_DIR, { recursive: true });
  fs.mkdirSync(BACKUPS, { recursive: true });
  if (!fs.existsSync(DATA)) {
    if (!fs.existsSync(SEED_DATA)) throw new Error('Falta el fitxer inicial data.json');
    fs.copyFileSync(SEED_DATA, DATA);
    if (fs.existsSync(CATALOG_DATA)) {
      const initial = JSON.parse(fs.readFileSync(DATA, 'utf8'));
      const catalog = JSON.parse(fs.readFileSync(CATALOG_DATA, 'utf8'));
      // ── CORRECCIÓ: afegir workCenter a entitats operatives del catàleg ────────
      const DEFAULT_WC = process.env.DEFAULT_WORK_CENTER || 'WC-CASA-MESTRES';
      const operatives = ['products', 'dishes', 'bases', 'documents', 'employees', 'reservations'];
      for (const key of operatives) {
        if (Array.isArray(catalog[key])) {
          catalog[key] = catalog[key].map(item =>
            item.workCenter ? item : { workCenter: DEFAULT_WC, ...item }
          );
        }
      }
      Object.assign(initial, catalog);
      fs.writeFileSync(DATA, JSON.stringify(initial, null, 2), 'utf8');
    }
  }
}

ensureStorage();

function securityHeaders(res) {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'SAMEORIGIN');
  res.setHeader('Referrer-Policy', 'same-origin');
  res.setHeader('Permissions-Policy', 'camera=(), microphone=(), geolocation=(self)');
}

function send(res, status, body, type = 'application/json; charset=utf-8') {
  securityHeaders(res);
  res.writeHead(status, { 'Content-Type': type, 'Cache-Control': 'no-store' });
  res.end(typeof body === 'string' ? body : JSON.stringify(body));
}

function safeEqual(left, right) {
  const a = Buffer.from(String(left));
  const b = Buffer.from(String(right));
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}

function hashSecret(value) {
  return crypto.createHash('sha256').update(String(value)).digest('hex');
}

function cookieValue(req, name) {
  const cookies = String(req.headers.cookie || '').split(';');
  for (const item of cookies) {
    const separator = item.indexOf('=');
    if (separator < 0) continue;
    if (item.slice(0, separator).trim() === name) return decodeURIComponent(item.slice(separator + 1).trim());
  }
  return '';
}

function activationAttemptKey(req, code) {
  const forwarded = String(req.headers['x-forwarded-for'] || '').split(',')[0].trim();
  return `${forwarded || req.socket?.remoteAddress || 'unknown'}:${String(code || '')}`;
}

function activationBlocked(req, code) {
  const key = activationAttemptKey(req, code);
  const current = deviceActivationAttempts.get(key);
  if (!current) return false;
  if (current.resetAt <= Date.now()) { deviceActivationAttempts.delete(key); return false; }
  return current.count >= 8;
}

function recordActivationFailure(req, code) {
  const key = activationAttemptKey(req, code);
  const current = deviceActivationAttempts.get(key);
  if (!current || current.resetAt <= Date.now()) deviceActivationAttempts.set(key, { count: 1, resetAt: Date.now() + 15 * 60 * 1000 });
  else current.count += 1;
}

function authenticatedEmployee(data, req) {
  const token = cookieValue(req, 'arcadi_employee_device');
  if (!token) return null;
  const tokenHash = hashSecret(token);
  return (data.employees || []).find(item => item.active !== false && item.deviceTokenHash && safeEqual(item.deviceTokenHash, tokenHash)) || null;
}

function sendEmployeeCookie(res, token, body) {
  securityHeaders(res);
  const secure = process.env.ARCADI_DESKTOP === '1' ? '' : '; Secure';
  res.writeHead(200, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
    'Set-Cookie': `arcadi_employee_device=${encodeURIComponent(token)}; Path=/; HttpOnly; SameSite=Strict; Max-Age=31536000${secure}`
  });
  res.end(JSON.stringify(body));
}

function adminConfigured() {
  return process.env.ARCADI_DESKTOP === '1' || Boolean(process.env.ADMIN_USER && process.env.ADMIN_PASSWORD);
}

function isAdmin(req) {
  if (process.env.ARCADI_DESKTOP === '1') {
    const address = String(req.socket?.remoteAddress || '');
    return ['127.0.0.1', '::1', '::ffff:127.0.0.1'].includes(address);
  }
  if (!adminConfigured()) return false;
  const header = String(req.headers.authorization || '');
  if (!header.startsWith('Basic ')) return false;
  let decoded = '';
  try {
    decoded = Buffer.from(header.slice(6), 'base64').toString('utf8');
  } catch {
    return false;
  }
  const separator = decoded.indexOf(':');
  if (separator < 0) return false;
  return safeEqual(decoded.slice(0, separator), process.env.ADMIN_USER)
    && safeEqual(decoded.slice(separator + 1), process.env.ADMIN_PASSWORD);
}

function requireAdmin(req, res) {
  if (!adminConfigured()) {
    send(res, 503, { error: "Configura ADMIN_USER i ADMIN_PASSWORD abans d'obrir el Back Office." });
    return false;
  }
  if (!isAdmin(req)) {
    res.setHeader('WWW-Authenticate', 'Basic realm="Casa Mestres Back Office", charset="UTF-8"');
    send(res, 401, { error: 'Accés restringit al Back Office.' });
    return false;
  }
  return true;
}

function normalizeArcadiData(data) {
  data.arcadiSchema = data.arcadiSchema || 'ARCADI_GESTIO_RESTAURANT_V1';
  const collections = [
    'maintenanceRecords', 'communications', 'crmContacts', 'marketingCampaigns', 'financialEntries',
    'groupEvents', 'experiences', 'loyaltyAccounts', 'organizations', 'governanceCriteria', 'corporateStandards', 'governanceTasks', 'criterionDeployments', 'communicationReads', 'appccTemplates', 'operatingProtocols', 'productStandards', 'supplierStandards', 'purchaseOrders',
    'goodsReceipts', 'traceabilityRecords', 'productionRecords', 'restaurants', 'permissions', 'permissionAudit',
    'platformProfiles', 'miniApps', 'dailyOperations', 'appliedMigrations'
  ];
  for (const key of collections) if (!Array.isArray(data[key])) data[key] = [];
  data.controlNormatiu = data.controlNormatiu && typeof data.controlNormatiu === 'object'
    ? data.controlNormatiu : { empresa: {}, records: {} };
  data.controlNormatiu.records = data.controlNormatiu.records && typeof data.controlNormatiu.records === 'object'
    ? data.controlNormatiu.records : {};
  if (!Array.isArray(data.controlNormatiu.records.recepcio)) data.controlNormatiu.records.recepcio = [];
  if (!data.restaurants.some(item => item.id === 'restaurant_casa_mestres')) {
    data.restaurants.unshift({
      id: 'restaurant_casa_mestres',
      name: data.company?.name || 'Casa Mestres',
      address: data.company?.address || '',
      phone: data.company?.phone || '',
      status: 'Actiu',
      notes: 'Centre principal'
    });
  }
  if (!data.organizations.some(item => item.id === 'company_casa_mestres')) {
    data.organizations.unshift({
      id: 'company_casa_mestres',
      name: data.company?.name || 'Casa Mestres',
      status: 'Activa',
      createdAt: new Date().toISOString()
    });
  }
  if (!data.organizations.some(item => item.id === 'company_grup_trafec')) {
    data.organizations.push({
      id: 'company_grup_trafec',
      name: 'Grup Tràfec',
      status: 'Activa',
      notes: 'Empresa corporativa dels centres Tràfec',
      createdAt: new Date().toISOString()
    });
  }
  const trafecNames = [
    'SARRIERA', 'SARRIERA1930', 'TRAFEC', "L'ARBOÇ",
    'LA GRANADA', 'SITGES', 'TRAFEC MAR', 'HOSPITALET', 'PISCINA', 'CAN CARTRO'
  ];
  for (const centre of data.restaurants) {
    const name = String(centre.name || '').toUpperCase()
      .replace(/À/g,'A').replace(/È/g,'E').replace(/É/g,'E')
      .replace(/Í/g,'I').replace(/Ï/g,'I').replace(/Ò/g,'O')
      .replace(/Ó/g,'O').replace(/Ú/g,'U').replace(/Ü/g,'U')
      .replace(/Ç/g,'C').replace(/·/g,'');
    if (name.includes('GRUP TRAFEC')) {
      centre.organizationId = 'company_grup_trafec';
      centre.kind = 'GROUP';
      centre.status = centre.status || 'Actiu';
      continue;
    }
    if (trafecNames.some(token => {
      const t = token.toUpperCase()
        .replace(/À/g,'A').replace(/È/g,'E').replace(/É/g,'E')
        .replace(/Í/g,'I').replace(/Ï/g,'I').replace(/Ò/g,'O')
        .replace(/Ó/g,'O').replace(/Ú/g,'U').replace(/Ü/g,'U')
        .replace(/Ç/g,'C').replace(/·/g,'');
      return name.includes(t);
    })) centre.organizationId = 'company_grup_trafec';
  }
  const casaMestresCentre = data.restaurants.find(item => item.id === 'restaurant_casa_mestres');
  if (casaMestresCentre && !casaMestresCentre.organizationId) casaMestresCentre.organizationId = 'company_casa_mestres';
  const defaultMiniApps = [
    { id: 'miniapp_reserves', name: 'Reserves', type: 'Reserves', path: '/reserves.html', status: 'Activa', notes: 'Mini app pública existent' },
    { id: 'miniapp_fitxatges', name: 'Fitxatges', type: 'RRHH', path: '/fitxatges.html', status: 'Activa', notes: 'Mini app de personal existent' }
  ];
  for (const item of defaultMiniApps) if (!data.miniApps.some(current => current.id === item.id)) data.miniApps.push(item);
  return data;
}

function readData() {
  try {
    return normalizeArcadiData(JSON.parse(fs.readFileSync(DATA, 'utf8')));
  } catch (error) {
    throw new Error(`No es pot llegir data.json: ${error.message}`);
  }
}

function backupCurrent() {
  if (!fs.existsSync(DATA)) return;
  fs.mkdirSync(BACKUPS, { recursive: true });
  const stamp = new Date().toISOString().replace(/[:.]/g, '-');
  fs.copyFileSync(DATA, path.join(BACKUPS, `data_${stamp}.json`));
  const files = fs.readdirSync(BACKUPS).filter(name => name.endsWith('.json')).sort().reverse();
  for (const file of files.slice(30)) fs.unlinkSync(path.join(BACKUPS, file));
}

function writeData(data) {
  data.updatedAt = new Date().toISOString();
  backupCurrent();
  const temporary = `${DATA}.tmp`;
  fs.writeFileSync(temporary, JSON.stringify(data, null, 2), 'utf8');
  fs.renameSync(temporary, DATA);
  return data;
}

let mutationQueue = Promise.resolve();
function mutateData(change) {
  const job = mutationQueue.then(async () => {
    const data = readData();
    const result = await change(data);
    writeData(data);
    return result;
  });
  mutationQueue = job.catch(() => {});
  return job;
}

const CRITERION_TARGETS = {
  BASE_RECIPE:       { collection: 'bases',            prefix: 'base',             kind: 'Base o recepta' },
  DISH_RECIPE:       { collection: 'dishes',           prefix: 'dish',             kind: 'Fitxa de plat' },
  APPCC_TEMPLATE:    { collection: 'appccTemplates',   prefix: 'appcc_template',   kind: 'Plantilla APPCC' },
  PRODUCT_STANDARD:  { collection: 'productStandards', prefix: 'product_standard', kind: 'Producte homologat' },
  SUPPLIER_STANDARD: { collection: 'supplierStandards',prefix: 'supplier_standard',kind: 'Proveïdor homologat' },
  OPERATING_PROTOCOL:{ collection: 'operatingProtocols',prefix: 'protocol',        kind: 'Protocol operatiu' }
};

function deployCriterion(data, criterion, actor) {
  const target = CRITERION_TARGETS[criterion.targetType];
  if (!target) throw Object.assign(new Error("Cal definir el tipus de resultat abans d'implantar"), { statusCode: 400 });
  const centreIds = Array.isArray(criterion.centreIds) ? criterion.centreIds : [];
  if (!centreIds.length) throw Object.assign(new Error('Cal seleccionar almenys un centre afectat'), { statusCode: 400 });
  data[target.collection] = data[target.collection] || [];
  data.criterionDeployments = data.criterionDeployments || [];
  const deployedAt = new Date().toISOString();
  const deployments = [];
  for (const centreId of centreIds) {
    const existingIdx = data[target.collection].findIndex(
      item => item.criterionId === criterion.id && item.centreId === centreId
    );
    const artifact = {
      id: existingIdx >= 0
        ? data[target.collection][existingIdx].id
        : `${target.prefix}_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 6)}`,
      criterionId: criterion.id,
      centreId,
      title: criterion.title || '',
      description: criterion.description || '',
      targetType: criterion.targetType,
      status: 'Actiu',
      deployedAt,
      deployedBy: actor || 'sistema',
      version: criterion.version || 1
    };
    if (existingIdx >= 0) data[target.collection][existingIdx] = artifact;
    else data[target.collection].push(artifact);
    const deployment = {
      id: `deploy_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 6)}`,
      criterionId: criterion.id,
      centreId,
      artifactId: artifact.id,
      artifactCollection: target.collection,
      deployedAt,
      deployedBy: actor || 'sistema',
      version: criterion.version || 1
    };
    data.criterionDeployments.push(deployment);
    deployments.push(deployment);
  }
  return deployments;
}

// ── Servidor HTTP ──────────────────────────────────────────────────────────────
const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
  const pathname = url.pathname;
  const method = req.method;

  // Health check
  if (pathname === '/api/health') {
    send(res, 200, { status: 'ok', timestamp: new Date().toISOString() });
    return;
  }

  // Fitxers estàtics
  if (method === 'GET' && !pathname.startsWith('/api/')) {
    const filePath = pathname === '/'
      ? path.join(PUBLIC, 'index.html')
      : path.join(PUBLIC, pathname.replace(/\.\./g, ''));
    if (fs.existsSync(filePath) && fs.statSync(filePath).isFile()) {
      const ext = path.extname(filePath).toLowerCase();
      const mimeTypes = {
        '.html': 'text/html; charset=utf-8',
        '.js':   'application/javascript; charset=utf-8',
        '.css':  'text/css; charset=utf-8',
        '.json': 'application/json; charset=utf-8',
        '.png':  'image/png', '.jpg': 'image/jpeg',
        '.svg':  'image/svg+xml', '.ico': 'image/x-icon',
        '.woff2':'font/woff2', '.woff': 'font/woff'
      };
      securityHeaders(res);
      res.writeHead(200, { 'Content-Type': mimeTypes[ext] || 'application/octet-stream' });
      res.end(fs.readFileSync(filePath));
      return;
    }
    // SPA fallback
    const indexPath = path.join(PUBLIC, 'index.html');
    if (fs.existsSync(indexPath)) {
      securityHeaders(res);
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(fs.readFileSync(indexPath));
      return;
    }
    send(res, 404, { error: 'Fitxer no trobat' });
    return;
  }

  // Llegir body
  let body = '';
  req.on('data', chunk => { body += chunk; });
  await new Promise(resolve => req.on('end', resolve));
  let parsed = {};
  if (body) {
    try { parsed = JSON.parse(body); } catch { send(res, 400, { error: 'JSON invàlid' }); return; }
  }

  // OAuth
  if (pathname.startsWith('/oauth/')) {
    const data = readData();
    handleOAuthRequest(req, res, data);
    return;
  }

  // MCP
  if (pathname === '/api/mcp' && method === 'POST') {
    if (!requireAdmin(req, res)) return;
    const data = readData();
    handleMcpRequest(req, res, data, writeData);
    return;
  }

  // Dades globals (admin)
  if (pathname === '/api/data' && method === 'GET') {
    if (!requireAdmin(req, res)) return;
    send(res, 200, readData());
    return;
  }
  if (pathname === '/api/data' && method === 'POST') {
    if (!requireAdmin(req, res)) return;
    await mutateData(data => { Object.assign(data, parsed); });
    send(res, 200, { ok: true });
    return;
  }

  // Reserves
  if (pathname === '/api/reservations' && method === 'GET') {
    const data = readData();
    const wc = url.searchParams.get('workCenter') || process.env.DEFAULT_WORK_CENTER || 'WC-CASA-MESTRES';
    send(res, 200, (data.reservations || []).filter(r => !r.workCenter || r.workCenter === wc));
    return;
  }
  if (pathname === '/api/reservations' && method === 'POST') {
    const DEFAULT_WC = process.env.DEFAULT_WORK_CENTER || 'WC-CASA-MESTRES';
    const result = await mutateData(data => {
      const reservation = {
        id: `res_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 7)}`,
        workCenter: parsed.workCenter || DEFAULT_WC,
        createdAt: new Date().toISOString(),
        ...parsed
      };
      data.reservations = data.reservations || [];
      data.reservations.push(reservation);
      return reservation;
    });
    send(res, 201, result);
    return;
  }

  // Fitxatges GPS
  if (pathname === '/api/punches' && method === 'POST') {
    const dataSnap = readData();
    const employee = authenticatedEmployee(dataSnap, req);
    if (!employee) { send(res, 401, { error: 'Cal autenticació' }); return; }
    const DEFAULT_WC = process.env.DEFAULT_WORK_CENTER || 'WC-CASA-MESTRES';
    const result = await mutateData(data => {
      const punch = {
        id: `punch_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 7)}`,
        workCenter: employee.workCenter || DEFAULT_WC,
        employeeId: employee.id,
        timestamp: new Date().toISOString(),
        ...parsed
      };
      data.punches = data.punches || [];
      data.punches.push(punch);
      return punch;
    });
    send(res, 201, result);
    return;
  }

  // Criteris de governança
  if (pathname === '/api/criteria' && method === 'GET') {
    if (!requireAdmin(req, res)) return;
    send(res, 200, readData().governanceCriteria || []);
    return;
  }
  if (pathname === '/api/criteria' && method === 'POST') {
    if (!requireAdmin(req, res)) return;
    const result = await mutateData(data => createCriterion(data, parsed));
    send(res, result.ok ? 201 : 400, result);
    return;
  }
  if (pathname.match(/^\/api\/criteria\/[^/]+$/) && method === 'PUT') {
    if (!requireAdmin(req, res)) return;
    const id = pathname.split('/')[3];
    const result = await mutateData(data => updateCriterion(data, id, parsed));
    send(res, result.ok ? 200 : 400, result);
    return;
  }
  if (pathname.match(/^\/api\/criteria\/[^/]+\/transition$/) && method === 'POST') {
    if (!requireAdmin(req, res)) return;
    const id = pathname.split('/')[3];
    const result = await mutateData(data => transitionCriterion(data, id, parsed));
    send(res, result.ok ? 200 : 400, result);
    return;
  }
  if (pathname.match(/^\/api\/criteria\/[^/]+\/deploy$/) && method === 'POST') {
    if (!requireAdmin(req, res)) return;
    const id = pathname.split('/')[3];
    const result = await mutateData(data => {
      const criterion = (data.governanceCriteria || []).find(c => c.id === id);
      if (!criterion) throw Object.assign(new Error('Criteri no trobat'), { statusCode: 404 });
      return deployCriterion(data, criterion, parsed.actor);
    });
    send(res, 200, { ok: true, deployments: result });
    return;
  }

  // Ruta no trobada
  send(res, 404, { error: `Ruta no trobada: ${method} ${pathname}` });
});

server.listen(PORT, HOST, () => {
  console.log(`[ARCADI] Servidor actiu a http://${HOST}:${PORT}`);
  console.log(`[ARCADI] DATA_DIR: ${DATA_DIR}`);
  console.log(`[ARCADI] DATA: ${DATA}`);
  console.log(`[ARCADI] CATALOG: ${CATALOG_DATA}`);
});