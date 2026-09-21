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
const CATALOG_DATA = path.join(ROOT, 'seed', 'catalog.json');
const SARRIERA_DATA = path.join(ROOT, 'seed', 'sarriera-kitchen-bases.json');
const DISH_RECIPE_DATA = path.join(ROOT, 'seed', 'dish-recipe-proposals.json');

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
    send(res, 503, { error: 'Configura ADMIN_USER i ADMIN_PASSWORD abans d’obrir el Back Office.' });
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
    'SARRIERA', 'SARRIERA1930', 'TRÀFEC', 'TRAFEC', 'L’ARBOÇ', "L'ARBOÇ",
    'LA GRANADA', 'SITGES', 'TRÀFEC MAR', 'HOSPITALET', 'PISCINA', 'CAN CARTRÓ', 'CAN CARTRO'
  ];
  for (const centre of data.restaurants) {
    const name = String(centre.name || '').toUpperCase();
    if (name.includes('GRUP TRÀFEC') || name.includes('GRUP TRAFEC')) {
      centre.organizationId = 'company_grup_trafec';
      centre.kind = 'GROUP';
      centre.status = centre.status || 'Actiu';
      continue;
    }
    if (trafecNames.some(token => name.includes(token))) centre.organizationId = 'company_grup_trafec';
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
  BASE_RECIPE: { collection: 'bases', prefix: 'base', kind: 'Base o recepta' },
  DISH_RECIPE: { collection: 'dishes', prefix: 'dish', kind: 'Fitxa de plat' },
  APPCC_TEMPLATE: { collection: 'appccTemplates', prefix: 'appcc_template', kind: 'Plantilla APPCC' },
  PRODUCT_STANDARD: { collection: 'productStandards', prefix: 'product_standard', kind: 'Producte homologat' },
  SUPPLIER_STANDARD: { collection: 'supplierStandards', prefix: 'supplier_standard', kind: 'Proveïdor homologat' },
  OPERATING_PROTOCOL: { collection: 'operatingProtocols', prefix: 'protocol', kind: 'Protocol operatiu' }
};

function deployCriterion(data, criterion, actor) {
  const target = CRITERION_TARGETS[criterion.targetType];
  if (!target) throw Object.assign(new Error('Cal definir el tipus de resultat abans d’implantar'), { statusCode: 400 });
  const centreIds = Array.isArray(criterion.centreIds) ? criterion.centreIds : [];
  if (!centreIds.length) throw Object.assign(new Error('Cal seleccionar almenys un centre afectat'), { statusCode: 400 });
  data[target.collection] = data[target.collection] || [];
  data.criterionDeployments = data.criterionDeployments || [];
  const now = new Date().toISOString();
  const results = [];
  for (const centreId of centreIds) {
    let deployment = data.criterionDeployments.find(item =>
      item.criterionId === criterion.id && item.criterionVersion === criterion.version && item.centreId === centreId
    );
    if (!deployment) {
      const operationalId = target.prefix + '_' + crypto.randomUUID();
      const operationalRecord = {
        id: operationalId,
        companyId: criterion.companyId,
        centreId,
        scope: 'CENTRE',
        name: criterion.title,
        title: criterion.title,
        description: criterion.problem,
        process: criterion.proposal,
        notes: criterion.proposal,
        status: 'PENDENT_VALIDACIO_LOCAL',
        sourceType: 'criterion',
        sourceId: criterion.id,
        sourceVersion: criterion.version,
        createdAt: now,
        updatedAt: now
      };
      data[target.collection].push(operationalRecord);
      deployment = {
        id: 'deployment_' + crypto.randomUUID(),
        criterionId: criterion.id,
        criterionVersion: criterion.version,
        companyId: criterion.companyId,
        centreId,
        targetType: criterion.targetType,
        targetCollection: target.collection,
        operationalId,
        status: 'PENDENT_ADOPCIO',
        createdBy: actor,
        createdAt: now,
        updatedAt: now,
        history: [{ at: now, actor, action: 'GENERAT' }]
      };
      data.criterionDeployments.push(deployment);
    }
    results.push(deployment);
  }
  return results;
}

const SARRIERA_MIGRATION = 'sarriera_kitchen_bases_2026_09_07_v1';

function cloneJson(value) {
  return JSON.parse(JSON.stringify(value));
}

function catalogName(value) {
  return String(value || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().trim();
}

function applyCatalogMigrations() {
  if (!fs.existsSync(SARRIERA_DATA)) return;
  const data = readData();
  data.appliedMigrations = Array.isArray(data.appliedMigrations) ? data.appliedMigrations : [];
  if (data.appliedMigrations.some(item => (typeof item === 'string' ? item : item?.id) === SARRIERA_MIGRATION)) return;

  const catalog = JSON.parse(fs.readFileSync(SARRIERA_DATA, 'utf8'));
  const productTemplates = Array.isArray(catalog.products) ? catalog.products : [];
  const baseTemplates = Array.isArray(catalog.bases) ? catalog.bases : [];
  const sourceProducts = productTemplates.filter(item => item.sourceMigration === SARRIERA_MIGRATION);
  data.products = Array.isArray(data.products) ? data.products : [];
  data.bases = Array.isArray(data.bases) ? data.bases : [];

  const productTemplateById = new Map(productTemplates.map(item => [item.id, item]));
  const productIdMap = new Map();
  const ensureProduct = template => {
    if (!template) return null;
    let current = data.products.find(item => item.id === template.id);
    if (!current) current = data.products.find(item => catalogName(item.name) === catalogName(template.name));
    if (!current) {
      current = cloneJson(template);
      current.price = 0;
      current.stock = 0;
      current.min = 0;
      current.supplierId = '';
      current.pricePending = true;
      const pending = 'Pendent de preu, format de compra i proveïdor; completar amb la primera recepció real.';
      current.notes = current.notes ? `${current.notes} ${pending}` : pending;
      data.products.push(current);
    } else if (template.sourceMigration) {
      current.sourceMigration = template.sourceMigration;
      if (current.purchasable === undefined) current.purchasable = template.purchasable !== false;
    }
    productIdMap.set(template.id, current.id);
    return current;
  };

  for (const template of sourceProducts) ensureProduct(template);
  for (const base of baseTemplates) {
    for (const ingredient of base.ingredients || []) {
      ensureProduct(productTemplateById.get(ingredient.productId));
    }
  }

  const baseIdMap = new Map();
  for (const template of baseTemplates) {
    let current = data.bases.find(item => item.id === template.id);
    if (!current) current = data.bases.find(item => catalogName(item.name) === catalogName(template.name));
    if (!current && template.id === 'base_catalog_12') {
      current = data.bases.find(item => catalogName(item.name) === 'roux');
    }
    if (!current) {
      current = { id: template.id, name: template.name, ingredients: [], baseUses: [] };
      data.bases.push(current);
    }
    baseIdMap.set(template.id, current.id);
  }

  for (const template of baseTemplates) {
    const currentId = baseIdMap.get(template.id);
    const current = data.bases.find(item => item.id === currentId);
    const migrated = cloneJson(template);
    migrated.id = current.id;
    migrated.ingredients = (migrated.ingredients || []).map(item => ({
      ...item,
      productId: productIdMap.get(item.productId) || item.productId
    }));
    migrated.baseUses = (migrated.baseUses || []).map(item => ({
      ...item,
      baseId: baseIdMap.get(item.baseId) || item.baseId
    }));
    if (!migrated.process && current.process) migrated.process = current.process;
    if (!migrated.life && current.life) migrated.life = current.life;
    Object.assign(current, migrated);
  }

  data.openingPurchaseConfig = {
    ...(data.openingPurchaseConfig || {}),
    ...(catalog.openingPurchaseConfig || {}),
    assumeZeroStock: true,
    pricePolicy: 'goods_receipt'
  };
  data.appliedMigrations.push({
    id: SARRIERA_MIGRATION,
    appliedAt: new Date().toISOString(),
    productsAddedOrLinked: sourceProducts.length,
    basesUpdated: baseTemplates.length
  });
  writeData(data);
  console.log(`Migració Sarriera aplicada: ${sourceProducts.length} productes i ${baseTemplates.length} bases.`);
}

applyCatalogMigrations();

function applyDishRecipeProposals() {
  if (!fs.existsSync(DISH_RECIPE_DATA)) return;
  const source = JSON.parse(fs.readFileSync(DISH_RECIPE_DATA, 'utf8'));
  const migrationId = source.migration || 'dish_recipe_proposals';
  const data = readData();
  data.appliedMigrations = Array.isArray(data.appliedMigrations) ? data.appliedMigrations : [];
  if (data.appliedMigrations.some(item => (typeof item === 'string' ? item : item?.id) === migrationId)) return;
  data.dishes = Array.isArray(data.dishes) ? data.dishes : [];
  data.products = Array.isArray(data.products) ? data.products : [];
  const productByName = name => {
    const wanted = catalogName(name);
    return data.products.find(item => {
      const current = catalogName(item.name);
      return current === wanted || current.includes(wanted) || wanted.includes(current);
    });
  };
  let updated = 0;
  let productsCreated = 0;
  const ensureProduct = ingredient => {
    let product = productByName(ingredient.name);
    if (product) return product;
    product = {
      id: 'product_recipe_' + crypto.createHash('sha1').update(catalogName(ingredient.name)).digest('hex').slice(0, 12),
      code: '',
      name: ingredient.name,
      family: 'Pendent de classificar',
      unit: ingredient.unit || 'g',
      price: 0,
      stock: 0,
      min: 0,
      active: true,
      notes: 'Creat per una proposta de recepta. Pendent de validar, classificar i valorar.',
      sourceMigration: migrationId
    };
    data.products.push(product);
    productsCreated += 1;
    return product;
  };
  for (const proposal of source.recipes || []) {
    const dish = data.dishes.find(item => item.id === proposal.id)
      || data.dishes.find(item => catalogName(item.name) === catalogName(proposal.name));
    if (!dish) continue;
    const alreadyDocumented = (dish.ingredients || []).length || (dish.baseUses || []).length || String(dish.process || '').trim();
    const generatedByRecipeMigration = String(dish.recipeProposalMigration || '').startsWith('dish_recipe_proposals_');
    if (alreadyDocumented && !generatedByRecipeMigration) continue;
    if (alreadyDocumented && generatedByRecipeMigration) {
      dish.recipeStatus = proposal.status || 'VALIDADA / REVISADA';
      dish.recipeProposalMigration = migrationId;
      dish.desc = String(dish.desc || '').replace('Proposta tècnica inicial generada a partir del nom del plat. Cal validar gramatges i procés abans d’usar-la com a recepta definitiva.', 'Recepta tècnica validada. Els gramatges, el procés i l’emplatat es poden ajustar des de la fitxa sense perdre la recepta.');
      updated += 1;
      continue;
    }
    dish.servings = dish.servings || proposal.servings || 1;
    dish.ingredients = (proposal.ingredients || []).map(item => {
      const product = ensureProduct(item);
      return { ...item, productId: product.id, name: product.name };
    });
    dish.baseUses = Array.isArray(dish.baseUses) ? dish.baseUses : [];
    dish.allergens = proposal.allergens || '';
    dish.desc = proposal.desc || '';
    dish.process = proposal.process || '';
    dish.plating = proposal.plating || '';
    dish.recipeStatus = proposal.status || 'PROPOSTA PENDENT DE VALIDACIÓ';
    dish.recipeProposalMigration = migrationId;
    updated += 1;
  }
  data.appliedMigrations.push({ id: migrationId, appliedAt: new Date().toISOString(), dishesUpdated: updated, productsCreated });
  writeData(data);
  console.log(`Propostes de recepta aplicades: ${updated} plats i ${productsCreated} ingredients pendents creats.`);
}

applyDishRecipeProposals();

function readRaw(req, limit = 25 * 1024 * 1024) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let size = 0;
    req.on('data', chunk => {
      size += chunk.length;
      if (size > limit) {
        reject(new Error('Fitxer massa gran'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

async function bodyJson(req, limit) {
  const raw = await readRaw(req, limit);
  try {
    return JSON.parse(raw.toString('utf8') || '{}');
  } catch {
    throw new Error('JSON no vàlid');
  }
}

function safeStatic(urlPath) {
  let pathname = decodeURIComponent(urlPath.split('?')[0]);
  if (pathname === '/' || pathname === '') pathname = '/index.html';
  const full = path.resolve(PUBLIC, `.${pathname}`);
  if (full !== PUBLIC && !full.startsWith(`${PUBLIC}${path.sep}`)) return null;
  return full;
}

function mime(file) {
  const extension = path.extname(file).toLowerCase();
  return ({
    '.html': 'text/html; charset=utf-8',
    '.js': 'application/javascript; charset=utf-8',
    '.css': 'text/css; charset=utf-8',
    '.json': 'application/json; charset=utf-8',
    '.png': 'image/png',
    '.jpg': 'image/jpeg',
    '.jpeg': 'image/jpeg',
    '.webp': 'image/webp',
    '.wasm': 'application/wasm',
    '.gz': 'application/gzip',
    '.txt': 'text/plain; charset=utf-8'
  })[extension] || 'application/octet-stream';
}

function norm(value) {
  return String(value || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().trim();
}

function menuPrice(menu) {
  if (Number.isFinite(Number(menu.reservationPrice))) return Number(menu.reservationPrice);
  if (Number.isFinite(Number(menu.priceNumeric))) return Number(menu.priceNumeric);
  const match = String(menu.price || '').replace(',', '.').match(/\d+(?:\.\d+)?/);
  return match ? Number(match[0]) : 0;
}

function nextProductCode(data, family, reserved = []) {
  const definition = (data.config?.families || []).find(item => item.name === family) || { prefix: 'ALT' };
  let maximum = 0;
  for (const product of [...(data.products || []), ...reserved]) {
    const match = String(product.code || '').match(new RegExp(`^${definition.prefix}-(\\d+)$`, 'i'));
    if (match) maximum = Math.max(maximum, Number(match[1]));
  }
  return `${definition.prefix}-${String(maximum + 1).padStart(3, '0')}`;
}

function haversine(lat1, lon1, lat2, lon2) {
  const radius = 6371000;
  const radians = value => value * Math.PI / 180;
  const deltaLat = radians(lat2 - lat1);
  const deltaLon = radians(lon2 - lon1);
  const value = Math.sin(deltaLat / 2) ** 2
    + Math.cos(radians(lat1)) * Math.cos(radians(lat2)) * Math.sin(deltaLon / 2) ** 2;
  return 2 * radius * Math.atan2(Math.sqrt(value), Math.sqrt(1 - value));
}

function publicBaseUrl(req) {
  const forwardedProtocol = String(req.headers['x-forwarded-proto'] || '').split(',')[0].trim();
  const protocol = forwardedProtocol || (req.socket.encrypted ? 'https' : 'http');
  const forwardedHost = String(req.headers['x-forwarded-host'] || '').split(',')[0].trim();
  const requestHost = forwardedHost || String(req.headers.host || '').trim();
  const requestBaseUrl = requestHost ? `${protocol}://${requestHost}`.replace(/\/$/, '') : '';

  // A Render, OAuth must advertise the exact public host used by ChatGPT.
  // Prefer the live request host so a stale APP_BASE_URL cannot break discovery.
  if (/\.onrender\.com(?::\d+)?$/i.test(requestHost)) return requestBaseUrl;

  const configured = String(process.env.APP_BASE_URL || '').trim().replace(/\/$/, '');
  return configured || requestBaseUrl;
}

function stripeRequest(method, endpoint, parameters = {}) {
  if (process.env.NODE_ENV === 'test' && process.env.STRIPE_TEST_MODE === 'mock') {
    if (method === 'POST' && endpoint === '/checkout/sessions') {
      const id = `cs_test_mock_${crypto.randomBytes(8).toString('hex')}`;
      const session = {
        id,
        url: `https://checkout.stripe.test/pay/${id}`,
        payment_status: 'unpaid',
        metadata: { reservation_id: parameters['metadata[reservation_id]'] || '' },
        payment_intent: `pi_test_${crypto.randomBytes(6).toString('hex')}`
      };
      stripeTestSessions.set(id, session);
      return Promise.resolve(session);
    }
    if (method === 'GET' && endpoint.startsWith('/checkout/sessions/')) {
      const id = decodeURIComponent(endpoint.split('/').pop());
      const session = stripeTestSessions.get(id);
      if (!session) return Promise.reject(new Error('Sessió Stripe de prova no trobada'));
      return Promise.resolve({ ...session, payment_status: 'paid' });
    }
  }

  return new Promise((resolve, reject) => {
    const clean = Object.fromEntries(Object.entries(parameters).filter(([, value]) => value !== undefined && value !== null && value !== ''));
    const body = new URLSearchParams(clean).toString();
    const isGet = method === 'GET';
    const requestPath = `/v1${endpoint}${isGet && body ? `?${body}` : ''}`;
    const headers = { Authorization: `Bearer ${process.env.STRIPE_SECRET_KEY || ''}` };
    if (!isGet) {
      headers['Content-Type'] = 'application/x-www-form-urlencoded';
      headers['Content-Length'] = Buffer.byteLength(body);
    }
    const request = https.request({ hostname: 'api.stripe.com', path: requestPath, method, headers }, response => {
      let chunks = '';
      response.on('data', chunk => { chunks += chunk; });
      response.on('end', () => {
        let parsed;
        try {
          parsed = JSON.parse(chunks);
        } catch {
          parsed = { error: { message: chunks || 'Resposta Stripe no vàlida' } };
        }
        if (response.statusCode >= 200 && response.statusCode < 300) resolve(parsed);
        else reject(new Error(parsed?.error?.message || 'Error Stripe'));
      });
    });
    request.on('error', reject);
    if (!isGet && body) request.write(body);
    request.end();
  });
}

function calculateDeposit(menu, pax) {
  const price = menuPrice(menu);
  const depositType = menu.depositType || 'fixed';
  const depositValue = Number(menu.depositValue || 0);
  const amount = depositType === 'percent' ? price * pax * depositValue / 100 : pax * depositValue;
  return {
    price,
    depositType,
    depositValue,
    depositAmount: Math.round(amount * 100) / 100
  };
}

async function createCheckoutSession(req, reservation, currency = 'EUR') {
  const base = publicBaseUrl(req);
  const parameters = {
    mode: 'payment',
    success_url: `${base}/reserves.html?stripe=success&session_id={CHECKOUT_SESSION_ID}`,
    cancel_url: `${base}/reserves.html?stripe=cancel&reservation_id=${encodeURIComponent(reservation.id)}&token=${encodeURIComponent(reservation.manageToken)}`,
    client_reference_id: reservation.id,
    customer_email: reservation.email,
    locale: 'auto',
    'metadata[reservation_id]': reservation.id,
    'line_items[0][quantity]': '1',
    'line_items[0][price_data][currency]': String(currency || 'EUR').toLowerCase(),
    'line_items[0][price_data][unit_amount]': String(Math.round(reservation.depositAmount * 100)),
    'line_items[0][price_data][product_data][name]': `Fiança reserva · ${reservation.menuTitle}`.slice(0, 127),
    'line_items[0][price_data][product_data][description]': `${reservation.date} ${reservation.time} · ${reservation.pax} pax`.slice(0, 127)
  };
  return stripeRequest('POST', '/checkout/sessions', parameters);
}

function verifyStripeSignature(rawBody, signatureHeader, secret) {
  const pieces = String(signatureHeader || '').split(',').map(piece => piece.trim().split('='));
  const timestamp = pieces.find(([key]) => key === 't')?.[1];
  const signatures = pieces.filter(([key]) => key === 'v1').map(([, value]) => value);
  if (!timestamp || !signatures.length) return false;
  if (Math.abs(Date.now() / 1000 - Number(timestamp)) > 300) return false;
  const expected = crypto.createHmac('sha256', secret).update(`${timestamp}.${rawBody.toString('utf8')}`).digest('hex');
  return signatures.some(signature => safeEqual(signature, expected));
}

function markSessionPaid(data, session) {
  const reservationId = session.metadata?.reservation_id;
  const reservation = (data.reservations || []).find(item => item.id === reservationId || item.stripeSessionId === session.id);
  if (!reservation) return null;
  if (session.payment_status === 'paid') {
    reservation.paymentStatus = 'pagat';
    reservation.status = 'Confirmada';
    reservation.paidAt = reservation.paidAt || new Date().toISOString();
    reservation.stripeSessionId = session.id;
    reservation.stripePaymentIntent = session.payment_intent || '';
    delete reservation.manageToken;
  }
  return reservation;
}

const ADMIN_STATIC = new Set(['/', '/index.html', '/app.js', '/ocr.html', '/control_normatiu.html']);

const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url, `http://${req.headers.host || HOST}`);
    const pathname = url.pathname;
    const baseUrl = publicBaseUrl(req);

    if (await handleOAuthRequest(req, res, url, baseUrl)) return;

    if (pathname === '/mcp') {
      const auth = authenticateBearer(req, baseUrl);
      return handleMcpRequest(req, res, {
        auth,
        readData,
        mutateData,
        getStatus: () => ({
          ok: true,
          app: 'ARCADI GESTIO RESTAURANT',
          connectorVersion: '0.5.1',
          serverTime: new Date().toISOString()
        }),
        challenge: (scope, error, description) => oauthChallenge(baseUrl, scope, error, description)
      });
    }

    if (pathname === '/api/health' && req.method === 'GET') {
      return send(res, 200, {
        ok: true,
      app: 'ARCADI GESTIO RESTAURANT',
        stripeConfigured: Boolean(process.env.STRIPE_SECRET_KEY),
        adminConfigured: adminConfigured(),
        persistence: configuredDataDir ? 'directori extern configurat' : 'fitxer local'
      });
    }

    if (pathname === '/api/stripe/webhook' && req.method === 'POST') {
      if (!process.env.STRIPE_WEBHOOK_SECRET) return send(res, 503, { error: 'Webhook Stripe no configurat' });
      const raw = await readRaw(req, 2 * 1024 * 1024);
      if (!verifyStripeSignature(raw, req.headers['stripe-signature'], process.env.STRIPE_WEBHOOK_SECRET)) {
        return send(res, 400, { error: 'Signatura Stripe no vàlida' });
      }
      const event = JSON.parse(raw.toString('utf8'));
      if (['checkout.session.completed', 'checkout.session.async_payment_succeeded'].includes(event.type)) {
        await mutateData(data => markSessionPaid(data, event.data.object));
      }
      return send(res, 200, { received: true });
    }

    if (pathname === '/api/state' && req.method === 'GET') {
      if (!requireAdmin(req, res)) return;
      return send(res, 200, readData());
    }

    if (pathname === '/api/state' && ['POST', 'PUT'].includes(req.method)) {
      if (!requireAdmin(req, res)) return;
      const incoming = await bodyJson(req);
      if (!incoming || typeof incoming !== 'object') return send(res, 400, { error: 'Dades no vàlides' });
      const state = await mutateData(current => {
        const reservations = current.reservations || [];
        const punches = current.punches || [];
        const dailyOperations = current.dailyOperations || [];
        const governanceCriteria = current.governanceCriteria || [];
        const corporateStandards = current.corporateStandards || [];
        const governanceTasks = current.governanceTasks || [];
        const criterionDeployments = current.criterionDeployments || [];
        const appccTemplates = current.appccTemplates || [];
        const operatingProtocols = current.operatingProtocols || [];
        const productStandards = current.productStandards || [];
        const supplierStandards = current.supplierStandards || [];
        const managedBases = (current.bases || []).filter(item => item.sourceType === 'criterion');
        const managedDishes = (current.dishes || []).filter(item => item.sourceType === 'criterion');
        incoming.bases = [...(incoming.bases || []).filter(item => item.sourceType !== 'criterion'), ...managedBases];
        incoming.dishes = [...(incoming.dishes || []).filter(item => item.sourceType !== 'criterion'), ...managedDishes];
        for (const key of Object.keys(current)) delete current[key];
        Object.assign(current, incoming, {
          reservations,
          punches,
          dailyOperations,
          governanceCriteria,
          corporateStandards,
          governanceTasks,
          criterionDeployments,
          appccTemplates,
          operatingProtocols,
          productStandards,
          supplierStandards
        });
        return current;
      });
      return send(res, 200, { ok: true, state });
    }

    if (pathname === '/api/criteria' && req.method === 'GET') {
      if (!requireAdmin(req, res)) return;
      const data = readData();
      const companyId = String(url.searchParams.get('companyId') || '').trim();
      const centreId = String(url.searchParams.get('centreId') || '').trim();
      const state = String(url.searchParams.get('state') || '').trim().toUpperCase();
      const items = (data.governanceCriteria || []).filter(item => {
        if (companyId && item.companyId !== companyId) return false;
        if (centreId && !(item.centreIds || []).includes(centreId) && !(item.optionalCentreIds || []).includes(centreId)) return false;
        if (state && item.state !== state) return false;
        return true;
      });
      return send(res, 200, { items });
    }

    if (pathname === '/api/criteria' && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const input = await bodyJson(req);
      const actor = String(process.env.ADMIN_USER || 'direccio');
      const criterion = await mutateData(data => {
        data.governanceCriteria = data.governanceCriteria || [];
        const created = createCriterion(input, actor);
        data.governanceCriteria.push(created);
        data.governanceTasks = data.governanceTasks || [];
        data.governanceTasks.push({
          id: 'criterion_task_' + crypto.randomUUID(),
          criterionId: created.id,
          companyId: created.companyId,
          centreId: '',
          title: created.nextStep || ('Definir criteri: ' + created.title),
          responsible: created.ownerId || '',
          dueDate: created.dueDate || '',
          status: 'PENDENT',
          type: 'PREPARACIO_CRITERI',
          createdAt: new Date().toISOString()
        });
        return created;
      });
      return send(res, 201, { ok: true, criterion });
    }

    const criterionMatch = pathname.match(/^\/api\/criteria\/([^/]+)$/);
    if (criterionMatch && req.method === 'PUT') {
      if (!requireAdmin(req, res)) return;
      const input = await bodyJson(req);
      const actor = String(process.env.ADMIN_USER || 'direccio');
      const criterion = await mutateData(data => {
        const found = (data.governanceCriteria || []).find(item => item.id === decodeURIComponent(criterionMatch[1]));
        if (!found) throw Object.assign(new Error('Criteri no trobat'), { statusCode: 404 });
        return updateCriterion(found, input, actor);
      });
      return send(res, 200, { ok: true, criterion });
    }

    const criterionTransitionMatch = pathname.match(/^\/api\/criteria\/([^/]+)\/transition$/);
    if (criterionTransitionMatch && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const input = await bodyJson(req);
      const actor = String(process.env.ADMIN_USER || 'direccio');
      const criterion = await mutateData(data => {
        const found = (data.governanceCriteria || []).find(item => item.id === decodeURIComponent(criterionTransitionMatch[1]));
        if (!found) throw Object.assign(new Error('Criteri no trobat'), { statusCode: 404 });
        const updated = transitionCriterion(found, input.state, actor, input.note);
        data.corporateStandards = data.corporateStandards || [];
        data.communications = data.communications || [];
        data.governanceTasks = data.governanceTasks || [];

        if (updated.state === 'APROVADA') {
          const existing = data.corporateStandards.find(item => item.criterionId === updated.id);
          const standard = {
            id: existing?.id || ('standard_' + crypto.randomUUID()),
            criterionId: updated.id,
            companyId: updated.companyId,
            centreIds: updated.centreIds || [],
            optionalCentreIds: updated.optionalCentreIds || [],
            type: updated.targetType || 'OPERATING_PROTOCOL',
            title: updated.title,
            content: updated.proposal,
            version: updated.version,
            status: 'APROVADA',
            effectiveAt: updated.effectiveAt,
            updatedAt: new Date().toISOString()
          };
          if (existing) Object.assign(existing, standard);
          else data.corporateStandards.push(standard);
        }

        if (updated.state === 'PUBLICADA' && !data.communications.some(item => item.sourceType === 'criterion' && item.sourceId === updated.id && item.criterionVersion === updated.version)) {
          data.communications.push({
            id: 'communication_' + crypto.randomUUID(),
            companyId: updated.companyId,
            centreIds: updated.centreIds || [],
            subject: 'Nou criteri publicat: ' + updated.title,
            channel: 'Intern',
            recipient: 'Centres afectats',
            status: 'Enviat',
            priority: updated.priority,
            message: updated.proposal,
            requiresAcknowledgement: true,
            sourceType: 'criterion',
            sourceId: updated.id,
            criterionVersion: updated.version,
            createdAt: new Date().toISOString()
          });
        }

        if (updated.state === 'EN_IMPLANTACIO') {
          deployCriterion(data, updated, actor);
          for (const centreId of updated.centreIds || []) {
            if (data.governanceTasks.some(item => item.criterionId === updated.id && item.centreId === centreId && item.type === 'IMPLANTACIO')) continue;
            data.governanceTasks.push({
              id: 'criterion_task_' + crypto.randomUUID(),
              criterionId: updated.id,
              companyId: updated.companyId,
              centreId,
              title: 'Implantar: ' + updated.title,
              responsible: '',
              dueDate: updated.dueDate || '',
              status: 'PENDENT',
              type: 'IMPLANTACIO',
              createdAt: new Date().toISOString()
            });
          }
        }
        return updated;
      });
      return send(res, 200, { ok: true, criterion });
    }

    const criterionExecuteMatch = pathname.match(/^\/api\/criteria\/([^/]+)\/execute$/);
    if (criterionExecuteMatch && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const actor = String(process.env.ADMIN_USER || 'direccio');
      const deployments = await mutateData(data => {
        const found = (data.governanceCriteria || []).find(item => item.id === decodeURIComponent(criterionExecuteMatch[1]));
        if (!found) throw Object.assign(new Error('Criteri no trobat'), { statusCode: 404 });
        if (!['PUBLICADA', 'EN_IMPLANTACIO', 'IMPLANTADA'].includes(found.state)) {
          throw Object.assign(new Error('El criteri s’ha de publicar abans de generar fitxes operatives'), { statusCode: 409 });
        }
        return deployCriterion(data, found, actor);
      });
      return send(res, 200, { ok: true, deployments });
    }

    const adoptionMatch = pathname.match(/^\/api\/criteria\/([^/]+)\/centres\/([^/]+)\/adoption$/);
    if (adoptionMatch && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const input = await bodyJson(req);
      const actor = String(process.env.ADMIN_USER || 'direccio');
      const deployment = await mutateData(data => {
        const criterionId = decodeURIComponent(adoptionMatch[1]);
        const centreId = decodeURIComponent(adoptionMatch[2]);
        const found = (data.criterionDeployments || []).find(item => item.criterionId === criterionId && item.centreId === centreId);
        if (!found) throw Object.assign(new Error('Implantació de centre no trobada'), { statusCode: 404 });
        const status = input.adopted === false ? 'REBUTJAT_LOCALMENT' : 'ADOPTAT';
        found.status = status;
        found.confirmedBy = String(input.confirmedBy || actor);
        found.confirmedAt = new Date().toISOString();
        found.notes = String(input.notes || '').trim();
        found.updatedAt = found.confirmedAt;
        found.history = found.history || [];
        found.history.push({ at: found.confirmedAt, actor, action: status, notes: found.notes });
        const operational = (data[found.targetCollection] || []).find(item => item.id === found.operationalId);
        if (operational) {
          operational.status = status === 'ADOPTAT' ? 'VIGENT' : 'REVISIO_NECESSARIA';
          operational.updatedAt = found.updatedAt;
        }
        const task = (data.governanceTasks || []).find(item => item.criterionId === criterionId && item.centreId === centreId && item.type === 'IMPLANTACIO');
        if (task && status === 'ADOPTAT') task.status = 'COMPLETADA';
        return found;
      });
      return send(res, 200, { ok: true, deployment });
    }

    if (pathname === '/api/control-state' && req.method === 'GET') {
      if (!requireAdmin(req, res)) return;
      return send(res, 200, readData().controlNormatiu || { empresa: {}, records: {} });
    }

    if (pathname === '/api/control-state' && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const control = await bodyJson(req);
      await mutateData(data => { data.controlNormatiu = control; });
      return send(res, 200, { ok: true });
    }

    if (pathname === '/api/products-bulk' && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const payload = await bodyJson(req);
      const rows = Array.isArray(payload.rows) ? payload.rows : [];
      const result = await mutateData(data => {
        data.products = data.products || [];
        let created = 0;
        let updated = 0;
        let skipped = 0;
        const reserved = [];
        for (const row of rows) {
          const name = String(row.name || '').trim();
          if (!name) {
            skipped += 1;
            continue;
          }
          const found = data.products.find(product => norm(product.name) === norm(name));
          if (found) {
            found.price = Number(row.price || 0);
            found.family = row.family || found.family || 'Altres';
            found.unit = row.unit || found.unit || 'unitat';
            found.subfamily = row.subfamily || found.subfamily || '';
            found.active = true;
            updated += 1;
            continue;
          }
          const family = row.family || 'Altres';
          const code = row.code || nextProductCode(data, family, reserved);
          const product = {
            id: `prod_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 7)}`,
            code,
            supplierCode: row.supplierCode || '',
            name,
            family,
            subfamily: row.subfamily || '',
            unit: row.unit || 'unitat',
            price: Number(row.price || 0),
            stock: 0,
            min: 0,
            supplierId: row.supplierId || '',
            location: '',
            notes: 'Creat des de l’OCR',
            active: true
          };
          data.products.push(product);
          reserved.push(product);
          created += 1;
        }
        return { created, updated, skipped };
      });
      return send(res, 200, { ok: true, ...result });
    }

    const employeeActivationMatch = pathname.match(/^\/api\/employees\/([^/]+)\/device-activation$/);
    if (employeeActivationMatch && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const employeeId = decodeURIComponent(employeeActivationMatch[1]);
      const activation = await mutateData(data => {
        const employee = (data.employees || []).find(item => item.id === employeeId);
        if (!employee) return null;
        const code = String(crypto.randomInt(100000, 1000000));
        employee.deviceActivationHash = hashSecret(code);
        employee.deviceActivationExpiresAt = new Date(Date.now() + 24 * 60 * 60 * 1000).toISOString();
        employee.deviceActivationCreatedAt = new Date().toISOString();
        return { code, employee: { id: employee.id, code: employee.code, name: employee.name, phone: employee.phone || '' }, expiresAt: employee.deviceActivationExpiresAt };
      });
      if (!activation) return send(res, 404, { error: 'Empleat no trobat' });
      return send(res, 200, { ok: true, ...activation });
    }

    const employeeUnlinkMatch = pathname.match(/^\/api\/employees\/([^/]+)\/device-unlink$/);
    if (employeeUnlinkMatch && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const employeeId = decodeURIComponent(employeeUnlinkMatch[1]);
      const unlinked = await mutateData(data => {
        const employee = (data.employees || []).find(item => item.id === employeeId);
        if (!employee) return false;
        delete employee.deviceTokenHash;
        delete employee.deviceActivatedAt;
        delete employee.deviceActivationHash;
        delete employee.deviceActivationExpiresAt;
        return true;
      });
      if (!unlinked) return send(res, 404, { error: 'Empleat no trobat' });
      return send(res, 200, { ok: true });
    }

    if (pathname === '/api/device-activate' && req.method === 'POST') {
      const input = await bodyJson(req);
      if (activationBlocked(req, input.code)) return send(res, 429, { error: 'Massa intents. Torna-ho a provar d’aquí a 15 minuts.' });
      const result = await mutateData(data => {
        const employee = (data.employees || []).find(item => String(item.code) === String(input.code) && item.active !== false);
        const activationHash = hashSecret(String(input.activationCode || ''));
        if (!employee || !employee.deviceActivationHash || !safeEqual(employee.deviceActivationHash, activationHash)) return null;
        if (!employee.deviceActivationExpiresAt || Date.parse(employee.deviceActivationExpiresAt) <= Date.now()) return null;
        const token = crypto.randomBytes(32).toString('base64url');
        employee.deviceTokenHash = hashSecret(token);
        employee.deviceActivatedAt = new Date().toISOString();
        delete employee.deviceActivationHash;
        delete employee.deviceActivationExpiresAt;
        delete employee.deviceActivationCreatedAt;
        delete employee.schedulePin;
        return { token, employee: { code: employee.code, name: employee.name } };
      });
      if (!result) {
        recordActivationFailure(req, input.code);
        return send(res, 401, { error: 'Codi d’empleat o activació incorrecte o caducat' });
      }
      deviceActivationAttempts.delete(activationAttemptKey(req, input.code));
      return sendEmployeeCookie(res, result.token, { ok: true, employee: result.employee });
    }

    if (pathname === '/api/device-session' && req.method === 'GET') {
      const data = readData();
      const employee = authenticatedEmployee(data, req);
      if (!employee) return send(res, 401, { error: 'Dispositiu no activat' });
      return send(res, 200, { ok: true, employee: { code: employee.code, name: employee.name, level: employee.level || '', role: employee.role || employee.roleBase || '' } });
    }

    if (pathname === '/api/employee-schedule' && req.method === 'POST') {
      const input = await bodyJson(req);
      const data = readData();
      const employee = authenticatedEmployee(data, req);
      if (!employee) return send(res, 401, { error: 'Aquest dispositiu no està activat' });
      const from = String(input.from || new Date().toISOString().slice(0, 10));
      const to = String(input.to || from);
      const items = (data.schedules || [])
        .filter(item => item.employeeId === employee.id && item.date >= from && item.date <= to)
        .sort((a, b) => String(a.date).localeCompare(String(b.date)))
        .map(item => ({ date: item.date, start: item.start || '', end: item.end || '', area: item.area || '', shiftCode: item.shiftCode || '', exception: item.exception === true, notes: item.notes || '' }));
      return send(res, 200, {
        employee: { code: employee.code, name: employee.name, level: employee.level || '', role: employee.role || employee.roleBase || '', tasks: employee.tasks || '', responsibilities: employee.responsibilities || '', notes: employee.notes || '' },
        from, to, items,
        communications: (data.communications || []).filter(item =>
          item.status !== 'Arxivat' &&
          (!item.companyId || item.companyId === employee.companyId) &&
          (!Array.isArray(item.centreIds) || !item.centreIds.length || item.centreIds.includes(employee.centreId))
        ).slice(-20).map(item => ({ subject: item.subject, message: item.message, priority: item.priority || '', createdAt: item.createdAt || '' }))
      });
    }

    if (pathname === '/api/punch' && req.method === 'POST') {
      const input = await bodyJson(req);
      const result = await mutateData(data => {
        data.punches = data.punches || [];
        const employee = authenticatedEmployee(data, req);
        if (!employee) return { error: 'Aquest dispositiu no està activat', status: 401 };
        if (!['ENTRADA', 'PAUSA', 'TORNAR', 'SORTIDA'].includes(String(input.type || ''))) {
          return { error: 'Tipus de fitxatge no vàlid', status: 400 };
        }
        const centre = (data.restaurants || []).find(item => item.id === employee.centreId);
        const gps = centre && Number.isFinite(Number(centre.gpsLat)) && Number.isFinite(Number(centre.gpsLng))
          ? { lat: centre.gpsLat, lng: centre.gpsLng, radius: centre.gpsRadius || 60 }
          : (data.company?.gps || {});
        if (![input.lat, input.lng, gps.lat, gps.lng].every(value => Number.isFinite(Number(value)))) {
          return { error: 'No es pot fitxar sense una ubicació GPS vàlida', status: 400 };
        }
        const accuracy = Number(input.accuracy);
        if (!Number.isFinite(accuracy) || accuracy > 100) {
          return { error: 'La precisió del GPS és insuficient. Apropa’t al local i torna-ho a provar.', status: 400 };
        }
        const distance = haversine(Number(input.lat), Number(input.lng), Number(gps.lat), Number(gps.lng));
        const radius = Number(gps.radius || 60);
        if (distance > radius) {
          return { error: `Fitxatge bloquejat: ets a ${Math.round(distance)} m del local (radi autoritzat: ${radius} m).`, status: 403 };
        }
        const status = 'DINS DE ZONA';
        const punch = {
          id: `punch_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 6)}`,
          employeeId: employee.id,
          employeeCode: employee.code,
          employeeName: employee.name,
          companyId: employee.companyId || centre?.organizationId || 'company_casa_mestres',
          centreId: employee.centreId || centre?.id || 'restaurant_casa_mestres',
          scope: 'CENTRE',
          type: input.type,
          dateTime: new Date().toISOString(),
          lat: input.lat ?? null,
          lng: input.lng ?? null,
          accuracy: input.accuracy ?? null,
          distance: distance === null ? null : Math.round(distance),
          status
        };
        data.punches.push(punch);
        return { punch };
      });
      if (result.error) return send(res, result.status, { error: result.error });
      return send(res, 200, { ok: true, punch: result.punch });
    }

    if (pathname === '/api/reservation-config' && req.method === 'GET') {
      const data = readData();
      const config = data.reservationConfig || {};
      const menus = (data.documents || [])
        .filter(item => item.type === 'Menú' && item.publishReservations === true)
        .map(item => ({
          id: item.id,
          title: item.title,
          subtitle: item.subtitle || '',
          price: menuPrice(item),
          depositType: item.depositType || 'fixed',
          depositValue: Number(item.depositValue || 0),
          notes: item.publicReservationNotes || item.notes || '',
          attachment: item.reservationAttachment || ''
        }));
      return send(res, 200, {
        company: {
          name: data.company?.name || 'Casa Mestres',
          phone: data.company?.phone || '',
          email: data.company?.email || '',
          logo: data.company?.logo || ''
        },
        config: {
          maxPax: Number(config.maxPax || 10),
          groupPhone: config.groupPhone || data.company?.phone || '',
          cancellationPolicy: config.cancellationPolicy || '',
          stripeEnabled: Boolean(process.env.STRIPE_SECRET_KEY),
          currency: config.currency || 'EUR'
        },
        menus
      });
    }

    if (pathname === '/api/reservation-config' && req.method === 'PUT') {
      if (!requireAdmin(req, res)) return;
      const input = await bodyJson(req);
      const config = await mutateData(data => {
        const current = data.reservationConfig || {};
        data.reservationConfig = {
          ...current,
          maxPax: Math.max(1, Number(input.maxPax || 10)),
          groupPhone: String(input.groupPhone || '').trim(),
          cancellationPolicy: String(input.cancellationPolicy || '').trim(),
          currency: String(input.currency || 'EUR').toUpperCase()
        };
        return data.reservationConfig;
      });
      return send(res, 200, { ok: true, config });
    }

    if (pathname === '/api/reservations' && req.method === 'POST') {
      const input = await bodyJson(req);
      const result = await mutateData(async data => {
        data.reservations = data.reservations || [];
        const config = data.reservationConfig || {};
        const maxPax = Number(config.maxPax || 10);
        const pax = Number(input.pax || 0);
        const name = String(input.name || '').trim();
        const phone = String(input.phone || '').trim();
        const email = String(input.email || '').trim();
        if (!input.date || !input.time || !name || !phone || !email) throw Object.assign(new Error('Falten dades obligatòries'), { statusCode: 400 });
        if (!/^\S+@\S+\.\S+$/.test(email)) throw Object.assign(new Error('L’email no és vàlid'), { statusCode: 400 });
        if (!input.termsAccepted) throw Object.assign(new Error('Cal acceptar les condicions de reserva i cancel·lació'), { statusCode: 400 });
        if (!Number.isInteger(pax) || pax < 1 || pax > maxPax) {
          throw Object.assign(new Error(`Per a més de ${maxPax} persones cal fer reserva de grup i contactar amb el restaurant.`), { statusCode: 400 });
        }
        const menu = (data.documents || []).find(item => item.id === input.menuId && item.type === 'Menú' && item.publishReservations === true);
        if (!menu) throw Object.assign(new Error('Menú no disponible'), { statusCode: 400 });
        const duplicate = data.reservations.find(item => item.date === input.date
          && norm(item.name) === norm(name)
          && !['cancel·lada', 'cancelled'].includes(norm(item.status)));
        if (duplicate) {
          throw Object.assign(new Error('Ja existeix una reserva amb aquest nom per aquest dia. Contacta amb el restaurant si necessites modificar-la.'), { statusCode: 409 });
        }
        const deposit = calculateDeposit(menu, pax);
        const reservation = {
          id: `res_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 7)}`,
          manageToken: crypto.randomBytes(18).toString('hex'),
          createdAt: new Date().toISOString(),
          date: input.date,
          time: input.time,
          pax,
          zone: input.zone || 'Sala principal',
          name,
          phone,
          email,
          menuId: menu.id,
          menuTitle: menu.title,
          menuPrice: deposit.price,
          depositType: deposit.depositType,
          depositValue: deposit.depositValue,
          depositAmount: deposit.depositAmount,
          status: deposit.depositAmount > 0 ? 'Pendent pagament' : 'Confirmada',
          paymentStatus: deposit.depositAmount > 0 ? 'pendent' : 'no requerit',
          marketing: Boolean(input.marketing),
          notes: String(input.notes || '').trim(),
          termsAcceptedAt: new Date().toISOString(),
          cancellationPolicy: String(config.cancellationPolicy || '')
        };
        let checkoutUrl = '';
        if (reservation.depositAmount > 0) {
          if (!process.env.STRIPE_SECRET_KEY) {
            throw Object.assign(new Error('El pagament online encara no està disponible. Contacta amb el restaurant.'), { statusCode: 503 });
          }
          const session = await createCheckoutSession(req, reservation, config.currency || 'EUR');
          reservation.stripeSessionId = session.id;
          checkoutUrl = session.url;
        }
        data.reservations.push(reservation);
        return { reservation, checkoutUrl };
      });
      return send(res, 200, {
        ok: true,
        reservation: result.reservation,
        checkoutUrl: result.checkoutUrl,
        stripeEnabled: Boolean(process.env.STRIPE_SECRET_KEY),
        message: result.checkoutUrl ? 'Reserva creada. Continua amb el pagament.' : 'Reserva confirmada sense fiança.'
      });
    }

    if (pathname === '/api/reservations/resume' && req.method === 'POST') {
      const input = await bodyJson(req);
      const result = await mutateData(async data => {
        const reservation = (data.reservations || []).find(item => item.id === input.reservationId && safeEqual(item.manageToken || '', input.token || ''));
        if (!reservation) throw Object.assign(new Error('No s’ha trobat la reserva pendent'), { statusCode: 404 });
        if (reservation.paymentStatus === 'pagat') throw Object.assign(new Error('Aquesta reserva ja està pagada'), { statusCode: 409 });
        if (!process.env.STRIPE_SECRET_KEY) throw Object.assign(new Error('Stripe no està configurat'), { statusCode: 503 });
        const config = data.reservationConfig || {};
        const session = await createCheckoutSession(req, reservation, config.currency || 'EUR');
        reservation.stripeSessionId = session.id;
        reservation.status = 'Pendent pagament';
        return { checkoutUrl: session.url };
      });
      return send(res, 200, { ok: true, checkoutUrl: result.checkoutUrl });
    }

    const statusMatch = pathname.match(/^\/api\/reservations\/([^/]+)\/status$/);
    if (statusMatch && req.method === 'PUT') {
      if (!requireAdmin(req, res)) return;
      const input = await bodyJson(req);
      const allowed = ['Pendent Stripe', 'Pendent pagament', 'Confirmada', 'Cancel·lada'];
      if (!allowed.includes(input.status)) return send(res, 400, { error: 'Estat no vàlid' });
      const reservation = await mutateData(data => {
        const found = (data.reservations || []).find(item => item.id === decodeURIComponent(statusMatch[1]));
        if (!found) throw Object.assign(new Error('Reserva no trobada'), { statusCode: 404 });
        found.status = input.status;
        if (input.status === 'Confirmada') found.paymentStatus = 'pagat';
        if (input.status === 'Cancel·lada' && found.paymentStatus !== 'pagat') found.paymentStatus = 'cancel·lat';
        return found;
      });
      return send(res, 200, { ok: true, reservation });
    }

    if (pathname === '/api/stripe/confirm' && req.method === 'GET') {
      if (!process.env.STRIPE_SECRET_KEY) return send(res, 400, { error: 'Stripe no està configurat' });
      const sessionId = url.searchParams.get('session_id');
      if (!sessionId) return send(res, 400, { error: 'Falta session_id' });
      const session = await stripeRequest('GET', `/checkout/sessions/${encodeURIComponent(sessionId)}`);
      const reservation = await mutateData(data => {
        const found = markSessionPaid(data, session);
        if (!found) throw Object.assign(new Error('Reserva no trobada'), { statusCode: 404 });
        return found;
      });
      return send(res, 200, { ok: true, paid: session.payment_status === 'paid', reservation });
    }

    if (pathname === '/api/restore' && req.method === 'POST') {
      if (!requireAdmin(req, res)) return;
      const incoming = await bodyJson(req);
      if (!incoming.schema || !incoming.company) return send(res, 400, { error: 'La còpia no correspon a l’app consolidada' });
      writeData(incoming);
      return send(res, 200, { ok: true });
    }

    if (pathname === '/api/backup' && req.method === 'GET') {
      if (!requireAdmin(req, res)) return;
      const content = fs.readFileSync(DATA);
      securityHeaders(res);
      res.writeHead(200, {
        'Content-Type': 'application/json; charset=utf-8',
        'Content-Disposition': `attachment; filename="CASA_MESTRES_BACKUP_${new Date().toISOString().slice(0, 10)}.json"`,
        'Cache-Control': 'no-store'
      });
      return res.end(content);
    }

    if (ADMIN_STATIC.has(pathname) && !requireAdmin(req, res)) return;
    const file = safeStatic(pathname);
    if (!file || !fs.existsSync(file) || !fs.statSync(file).isFile()) return send(res, 404, 'No trobat', 'text/plain; charset=utf-8');
    securityHeaders(res);
    res.writeHead(200, { 'Content-Type': mime(file), 'Cache-Control': 'no-cache' });
    return fs.createReadStream(file).pipe(res);
  } catch (error) {
    return send(res, error.statusCode || 500, { error: error.message });
  }
});

server.listen(PORT, HOST, () => {
  const localHost = HOST === '0.0.0.0' ? '127.0.0.1' : HOST;
  const url = `http://${localHost}:${PORT}`;
  console.log(`ARCADI GESTIO RESTAURANT: ${url}`);
  if (process.platform === 'win32' && !process.env.NO_OPEN) {
    setTimeout(() => exec(`start "" "${url}"`), 600);
  }
});

module.exports = { server };
