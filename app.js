const ZETA_DIGITS = "16449340668482264364724151666460251892189499012067984377355582293700074704032008738336289006197587053040043189623371906796287246870050077879351029463308662768317333093677626050952510068721400547968115587948903608232777619198407564558769632356367097100969489020859320080516364788783388460444451840598251452506833876314227658793929588063204472197908477340910590208378289549278263890379763583343942045159120818099593454448774587965008808894087011116347106931614618428879815486244835909183448757387428394082760287563214346010013576620982048720690400073826635603024022844629630324566097171951427721315951255679986190871931543953524106380440721421339654750580158723165839947624349142243348362904887009665059862263034109596736552811371670326911498784034357161605776676333067252736894238416640889536227595400772794748127102520498378433230017165744810302860434966884794216728433597281997793810008466560780537782885947278625931618664588292160658193859232415325806461781201884649777625984977560609384606051467685834725623197101836301479837488962159297027632358745738223006797795679319515651996612383618366168655665797003758579395038193467059393114859491596635058620858526381064548879582000789743717215693657490825080352045741139287635530947709860823922939866707500525803645340315412739072742722890227479742157521265272866790504356086447019522174348296308095407209404388845394174205278719269341962282024749751511874134727875179936647336874820752335660885793907659619607908126511591050729219558844613572641252614751578071609175156885327683293665654765588128436115113494859670092266296975220677781810295008702914015225183747431377217755317906719967001114954768292364207502705341165049051072861188854707754573575854747032957919907087156125812402558853000196898875722439717953811180793070896494335953356183275794651103546695668292833094507406208425346300827605686180238175238239659462458207920249063737872085300479379967603565543851521312093605893490413075491311959041935877531888380567912171377264570722995635142812810658216832092872867483537830128254732917028021436897618019637363184980566899586355341068647425930801883367749469866838428949777402705311753583758607474169405737637153525165870187112803861643246178480126671392369158545043444646648471950875283006191625838679257789892298444165212547711817391890576286084578861368469335293800824741929432439323626468769086749231576094206150249840056930228249239061832435185795019030056175145835716574335223282351666140476391283940576264724881002052041812033788626252366555788937763981538291415976032314805706590691944583703140205153805821921917295905553978794000789946";

const ZETA_DECIMAL_DIGITS = ZETA_DIGITS.slice(1);
const MASK64 = (1n << 64n) - 1n;
const MAGIC = [0x5a, 0x32, 0x43, 0x32]; // Z2C2
const CARRIER_MAGIC = [0x5a, 0x52, 0x57, 0x31]; // ZRW1
const DEFAULT_ITERATIONS = 250000;
const MAX_MESSAGE_BYTES = 6000;

const CELL_SIZE = 28;
const ROW_GAP = 4;
const MARGIN = 28;
const LINE_RADIUS = 1;
const MAX_COLS = 72;
const TEMPLATE_POINT_COUNT = CELL_SIZE * CELL_SIZE;

let generatedPngName = '';
let loadedPngImageData = null;
let templateTable = null;
let templateMaps = null;

const $ = (id) => document.getElementById(id);
const refs = {
  messageInput: $('messageInput'),
  encodePassword: $('encodePassword'),
  decodePassword: $('decodePassword'),
  plainOutput: $('plainOutput'),
  statusText: $('statusText'),
  encodeCanvas: $('encodeCanvas'),
  decodeCanvas: $('decodeCanvas'),
  encodeInfo: $('encodeInfo'),
  decodeInfo: $('decodeInfo'),
  loadPngFile: $('loadPngFile'),
  savePngBtn: $('savePngBtn'),
};

function setStatus(message, type = '') {
  refs.statusText.textContent = message;
  refs.statusText.className = type ? `status ${type}` : 'status';
}

function utf8Bytes(text) {
  return new TextEncoder().encode(text);
}

function rotl(x, k) {
  return ((x << BigInt(k)) | (x >> BigInt(64 - k))) & MASK64;
}

function read64(bytes, offset) {
  let v = 0n;
  for (let i = 0; i < 8; i++) v |= BigInt(bytes[offset + i] || 0) << BigInt(i * 8);
  return v & MASK64;
}

class Xoshiro256StarStar {
  constructor(seedBytes) {
    this.s = [read64(seedBytes, 0), read64(seedBytes, 8), read64(seedBytes, 16), read64(seedBytes, 24)];
    if (this.s.every(v => v === 0n)) this.s[0] = 0x9e3779b97f4a7c15n;
  }
  next() {
    const result = (rotl((this.s[1] * 5n) & MASK64, 7) * 9n) & MASK64;
    const t = (this.s[1] << 17n) & MASK64;
    this.s[2] ^= this.s[0];
    this.s[3] ^= this.s[1];
    this.s[1] ^= this.s[2];
    this.s[0] ^= this.s[3];
    this.s[2] ^= t;
    this.s[3] = rotl(this.s[3], 45);
    return result;
  }
}

function concatBytes(...arrays) {
  const total = arrays.reduce((n, a) => n + a.length, 0);
  const out = new Uint8Array(total);
  let p = 0;
  for (const a of arrays) { out.set(a, p); p += a.length; }
  return out;
}

function uint32Bytes(n) {
  return new Uint8Array([(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
}

function readUint32(bytes, pos) {
  return ((bytes[pos] << 24) | (bytes[pos + 1] << 16) | (bytes[pos + 2] << 8) | bytes[pos + 3]) >>> 0;
}

async function sha256(bytes) {
  return new Uint8Array(await crypto.subtle.digest('SHA-256', bytes));
}

async function deriveSeed(password, salt, iterations) {
  const material = await crypto.subtle.importKey('raw', utf8Bytes(password), 'PBKDF2', false, ['deriveBits']);
  const bits = await crypto.subtle.deriveBits({ name: 'PBKDF2', salt, iterations, hash: 'SHA-256' }, material, 256);
  return new Uint8Array(bits);
}

function zetaDigit(line, digit, mix) {
  const m = BigInt(ZETA_DECIMAL_DIGITS.length);
  const idx = Number((BigInt(line) * 1315423911n + BigInt(digit) * 2654435761n + (mix & 0xffffffffn)) % m);
  return ZETA_DECIMAL_DIGITS.charCodeAt(idx) - 48;
}

function makeKeystream(length, seedBytes) {
  const rng = new Xoshiro256StarStar(seedBytes);
  const stream = new Uint8Array(length);
  for (let i = 0; i < length; i++) {
    let b = 0;
    for (let bit = 0; bit < 8; bit++) {
      const a = rng.next();
      const c = rng.next();
      const line = 1000000 + Number(a % 900000000n);
      const digit = 1 + Number(c % BigInt(Math.min(1800, ZETA_DECIMAL_DIGITS.length - 1)));
      const invert = Number((c >> 23n) & 1n);
      const zd = zetaDigit(line, digit, a ^ c);
      const bitVal = (zd & 1) ^ invert;
      b |= bitVal << bit;
    }
    stream[i] = b;
  }
  return stream;
}

function xorBytes(a, b) {
  const out = new Uint8Array(a.length);
  for (let i = 0; i < a.length; i++) out[i] = a[i] ^ b[i];
  return out;
}

function crc32(bytes) {
  let crc = 0xffffffff;
  for (let i = 0; i < bytes.length; i++) {
    crc ^= bytes[i];
    for (let j = 0; j < 8; j++) crc = (crc >>> 1) ^ (0xedb88320 & -(crc & 1));
  }
  return (crc ^ 0xffffffff) >>> 0;
}

function buildCarrierBytes({ salt, iterations, cipher }) {
  const header = concatBytes(
    new Uint8Array(CARRIER_MAGIC),
    new Uint8Array([1, 0]),
    uint32Bytes(iterations >>> 0),
    salt,
    uint32Bytes(cipher.length >>> 0),
    cipher
  );
  return concatBytes(header, uint32Bytes(crc32(header)));
}

function parseCarrierBytes(bytes) {
  if (bytes.length < 34) throw new Error('PNGデータが短すぎます。');
  for (let i = 0; i < 4; i++) if (bytes[i] !== CARRIER_MAGIC[i]) throw new Error('ZETA TRACE PNGではありません。');
  if (bytes[4] !== 1) throw new Error('未対応のPNGバージョンです。');
  const iterations = readUint32(bytes, 6);
  const salt = bytes.slice(10, 26);
  const cipherLength = readUint32(bytes, 26);
  const end = 30 + cipherLength;
  const crcPos = end;
  if (bytes.length < crcPos + 4) throw new Error('PNG内のデータが途中で切れています。');
  const body = bytes.slice(0, crcPos);
  const expected = readUint32(bytes, crcPos);
  const actual = crc32(body);
  if (expected !== actual) throw new Error('PNGからデータを正しく復元できません。');
  return { iterations, salt, cipher: bytes.slice(30, end), carrierLength: crcPos + 4 };
}

function zetaStageShift(stage) {
  const idx = (stage * 73 + 41) % ZETA_DECIMAL_DIGITS.length;
  return (ZETA_DECIMAL_DIGITS.charCodeAt(idx) - 48) & 3;
}

function setBitmapPixel(bitmap, x, y) {
  if (x < 0 || y < 0 || x >= CELL_SIZE || y >= CELL_SIZE) return;
  bitmap[y * CELL_SIZE + x] = 1;
}

function setThickPixel(bitmap, x, y) {
  for (let dy = -LINE_RADIUS; dy <= LINE_RADIUS; dy++) {
    for (let dx = -LINE_RADIUS; dx <= LINE_RADIUS; dx++) {
      setBitmapPixel(bitmap, x + dx, y + dy);
    }
  }
}

function drawLineToBitmap(bitmap, x0, y0, x1, y1) {
  x0 = Math.round(x0); y0 = Math.round(y0); x1 = Math.round(x1); y1 = Math.round(y1);
  let dx = Math.abs(x1 - x0);
  let sx = x0 < x1 ? 1 : -1;
  let dy = -Math.abs(y1 - y0);
  let sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  while (true) {
    setThickPixel(bitmap, x0, y0);
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
}

function makeTemplateBitmap(byte, mirrored = false) {
  // v0.2: each encrypted byte becomes a denser 8-step walk.
  // The high/low vertical bands keep decoding stable, while zeta jitter softens the repeated cell feel.
  const topBand = [6, 8, 5, 9, 7, 6, 8, 5];
  const bottomBand = [21, 18, 22, 19, 20, 22, 18, 21];
  const points = [[0, 14]];

  for (let stage = 0; stage < 8; stage++) {
    const bit = (byte >> (7 - stage)) & 1;
    const zi = (byte * 37 + stage * 113 + zetaStageShift(stage) * 19 + 17) % ZETA_DECIMAL_DIGITS.length;
    const zd = ZETA_DECIMAL_DIGITS.charCodeAt(zi) - 48;
    const jitter = (zd % 3) - 1;
    const x = 3 + stage * 3;
    const y = (bit ? bottomBand[stage] : topBand[stage]) + jitter;
    points.push([x, y]);
  }

  points.push([27, 14]);

  const bitmap = new Uint8Array(TEMPLATE_POINT_COUNT);
  for (let i = 0; i < points.length - 1; i++) {
    let [x0, y0] = points[i];
    let [x1, y1] = points[i + 1];
    if (mirrored) { x0 = CELL_SIZE - 1 - x0; x1 = CELL_SIZE - 1 - x1; }
    drawLineToBitmap(bitmap, x0, y0, x1, y1);
  }
  return bitmap;
}

function isComparableTemplatePixel(index) {
  const x = index % CELL_SIZE;
  // Row-wrap connectors touch the outer edge of a cell.
  // Keep those edge pixels visual-only so PNG reading remains stable.
  return x >= 2 && x < CELL_SIZE - 2;
}

function hashBitmap(bitmap) {
  let h = 2166136261 >>> 0;
  for (let i = 0; i < bitmap.length; i++) {
    if (!isComparableTemplatePixel(i)) continue;
    h ^= bitmap[i];
    h = Math.imul(h, 16777619) >>> 0;
  }
  return h.toString(16);
}

function hammingDistance(a, b) {
  let d = 0;
  for (let i = 0; i < a.length; i++) {
    if (!isComparableTemplatePixel(i)) continue;
    if (a[i] !== b[i]) d++;
  }
  return d;
}

function buildTemplates() {
  const normal = [];
  const mirrored = [];
  const normalMap = new Map();
  const mirroredMap = new Map();
  for (let byte = 0; byte < 256; byte++) {
    const nb = makeTemplateBitmap(byte, false);
    const mb = makeTemplateBitmap(byte, true);
    normal.push(nb);
    mirrored.push(mb);
    normalMap.set(hashBitmap(nb), byte);
    mirroredMap.set(hashBitmap(mb), byte);
  }
  return { normal, mirrored, normalMap, mirroredMap };
}

function ensureTemplates() {
  if (!templateTable) {
    templateTable = buildTemplates();
    templateMaps = templateTable;
  }
  return templateTable;
}

function computeLayout(byteLength) {
  const cols = Math.min(MAX_COLS, Math.max(1, Math.ceil(Math.sqrt(byteLength * 1.35))));
  const rows = Math.ceil(byteLength / cols);
  const padded = rows * cols;
  const width = MARGIN * 2 + cols * CELL_SIZE;
  const height = MARGIN * 2 + rows * CELL_SIZE + Math.max(0, rows - 1) * ROW_GAP;
  return { cols, rows, padded, width, height };
}

function whiteImageData(width, height) {
  const imageData = new ImageData(width, height);
  const d = imageData.data;
  for (let i = 0; i < d.length; i += 4) {
    d[i] = 255; d[i + 1] = 255; d[i + 2] = 255; d[i + 3] = 255;
  }
  return imageData;
}

function drawBitmapAt(imageData, bitmap, ox, oy) {
  const data = imageData.data;
  const width = imageData.width;
  for (let y = 0; y < CELL_SIZE; y++) {
    for (let x = 0; x < CELL_SIZE; x++) {
      if (!bitmap[y * CELL_SIZE + x]) continue;
      const px = ox + x;
      const py = oy + y;
      const p = (py * width + px) * 4;
      data[p] = 0; data[p + 1] = 0; data[p + 2] = 0; data[p + 3] = 255;
    }
  }
}

function drawThickLineImageData(imageData, x0, y0, x1, y1) {
  const bitmap = new Uint8Array(imageData.width * imageData.height);
  const oldCell = CELL_SIZE;
  // Simple local Bresenham directly on the full image.
  x0 = Math.round(x0); y0 = Math.round(y0); x1 = Math.round(x1); y1 = Math.round(y1);
  let dx = Math.abs(x1 - x0);
  let sx = x0 < x1 ? 1 : -1;
  let dy = -Math.abs(y1 - y0);
  let sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  const put = (x, y) => {
    const data = imageData.data;
    for (let yy = -LINE_RADIUS; yy <= LINE_RADIUS; yy++) {
      for (let xx = -LINE_RADIUS; xx <= LINE_RADIUS; xx++) {
        const px = x + xx;
        const py = y + yy;
        if (px < 0 || py < 0 || px >= imageData.width || py >= imageData.height) continue;
        const p = (py * imageData.width + px) * 4;
        data[p] = 0; data[p + 1] = 0; data[p + 2] = 0; data[p + 3] = 255;
      }
    }
  };
  while (true) {
    put(x0, y0);
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
}

function renderWalkPngToCanvas(canvas, carrierBytes) {
  const templates = ensureTemplates();
  const layout = computeLayout(carrierBytes.length);
  const padded = new Uint8Array(layout.padded);
  padded.set(carrierBytes);

  canvas.width = layout.width;
  canvas.height = layout.height;
  const ctx = canvas.getContext('2d', { willReadFrequently: true });
  const imageData = whiteImageData(layout.width, layout.height);

  let index = 0;
  for (let row = 0; row < layout.rows; row++) {
    const rtl = row % 2 === 1;
    for (let colInOrder = 0; colInOrder < layout.cols; colInOrder++) {
      const col = rtl ? layout.cols - 1 - colInOrder : colInOrder;
      const x = MARGIN + col * CELL_SIZE;
      const y = MARGIN + row * (CELL_SIZE + ROW_GAP);
      const byte = padded[index++];
      drawBitmapAt(imageData, rtl ? templates.mirrored[byte] : templates.normal[byte], x, y);
    }
    if (row < layout.rows - 1) {
      const edgeCol = rtl ? 0 : layout.cols - 1;
      const x = MARGIN + edgeCol * CELL_SIZE + (rtl ? 0 : CELL_SIZE - 1);
      const y0 = MARGIN + row * (CELL_SIZE + ROW_GAP) + Math.floor(CELL_SIZE / 2);
      const y1 = MARGIN + (row + 1) * (CELL_SIZE + ROW_GAP) + Math.floor(CELL_SIZE / 2);
      drawThickLineImageData(imageData, x, y0, x, y1);
    }
  }

  ctx.putImageData(imageData, 0, 0);
  return layout;
}

function extractCellBitmap(imageData, x0, y0) {
  const bitmap = new Uint8Array(TEMPLATE_POINT_COUNT);
  const data = imageData.data;
  const width = imageData.width;
  for (let y = 0; y < CELL_SIZE; y++) {
    for (let x = 0; x < CELL_SIZE; x++) {
      const p = ((y0 + y) * width + (x0 + x)) * 4;
      const lum = (data[p] + data[p + 1] + data[p + 2]) / 3;
      bitmap[y * CELL_SIZE + x] = lum < 128 ? 1 : 0;
    }
  }
  return bitmap;
}

function inferLayoutFromImage(width, height) {
  if (width <= MARGIN * 2 || height <= MARGIN * 2) throw new Error('PNGサイズが不正です。');
  const colsFloat = (width - MARGIN * 2) / CELL_SIZE;
  if (!Number.isInteger(colsFloat) || colsFloat < 1 || colsFloat > MAX_COLS) throw new Error('PNGレイアウトを認識できません。');
  const cols = colsFloat;
  const rowsFloat = (height - MARGIN * 2 + ROW_GAP) / (CELL_SIZE + ROW_GAP);
  if (!Number.isInteger(rowsFloat) || rowsFloat < 1) throw new Error('PNGレイアウトを認識できません。');
  const rows = rowsFloat;
  return { cols, rows, padded: cols * rows, width, height };
}

function matchTemplate(bitmap, mirrored) {
  const templates = ensureTemplates();
  const h = hashBitmap(bitmap);
  const direct = mirrored ? templates.mirroredMap.get(h) : templates.normalMap.get(h);
  if (direct !== undefined) return direct;

  let bestByte = -1;
  let bestDistance = Infinity;
  const table = mirrored ? templates.mirrored : templates.normal;
  for (let byte = 0; byte < 256; byte++) {
    const d = hammingDistance(bitmap, table[byte]);
    if (d < bestDistance) { bestDistance = d; bestByte = byte; }
  }
  if (bestDistance <= 18) return bestByte;
  throw new Error('PNGの線パターンを読み取れません。');
}

function carrierBytesFromImageData(imageData) {
  const layout = inferLayoutFromImage(imageData.width, imageData.height);
  const bytes = [];
  for (let row = 0; row < layout.rows; row++) {
    const rtl = row % 2 === 1;
    for (let colInOrder = 0; colInOrder < layout.cols; colInOrder++) {
      const col = rtl ? layout.cols - 1 - colInOrder : colInOrder;
      const x = MARGIN + col * CELL_SIZE;
      const y = MARGIN + row * (CELL_SIZE + ROW_GAP);
      const bitmap = extractCellBitmap(imageData, x, y);
      bytes.push(matchTemplate(bitmap, rtl));
    }
  }
  return new Uint8Array(bytes);
}

function imageFileToImageData(file, canvas) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    const url = URL.createObjectURL(file);
    img.onload = () => {
      URL.revokeObjectURL(url);
      canvas.width = img.naturalWidth;
      canvas.height = img.naturalHeight;
      const ctx = canvas.getContext('2d', { willReadFrequently: true });
      ctx.imageSmoothingEnabled = false;
      ctx.clearRect(0, 0, canvas.width, canvas.height);
      ctx.drawImage(img, 0, 0);
      resolve(ctx.getImageData(0, 0, canvas.width, canvas.height));
    };
    img.onerror = () => {
      URL.revokeObjectURL(url);
      reject(new Error('PNGを読み込めませんでした。'));
    };
    img.src = url;
  });
}

async function createCipherFromMessage(message, password) {
  const messageBytes = utf8Bytes(message);
  if (messageBytes.length > MAX_MESSAGE_BYTES) throw new Error(`${MAX_MESSAGE_BYTES} bytes以内にしてください。`);
  const salt = crypto.getRandomValues(new Uint8Array(16));
  const seed = await deriveSeed(password, salt, DEFAULT_ITERATIONS);
  const digest = (await sha256(messageBytes)).slice(0, 8);
  const payload = concatBytes(new Uint8Array(MAGIC), uint32Bytes(messageBytes.length), digest, messageBytes);
  const stream = makeKeystream(payload.length, seed);
  const cipher = xorBytes(payload, stream);
  return { salt, cipher, messageBytes };
}

async function decodeCipherToMessage(cipher, salt, iterations, password) {
  const seed = await deriveSeed(password, salt, iterations);
  const stream = makeKeystream(cipher.length, seed);
  const plain = xorBytes(cipher, stream);

  for (let i = 0; i < MAGIC.length; i++) {
    if (plain[i] !== MAGIC[i]) throw new Error('復号できません。');
  }

  const len = readUint32(plain, 4);
  if (len > plain.length - 16) throw new Error('復号できません。');

  const digest = plain.slice(8, 16);
  const msgBytes = plain.slice(16, 16 + len);
  const check = (await sha256(msgBytes)).slice(0, 8);
  for (let i = 0; i < 8; i++) {
    if (digest[i] !== check[i]) throw new Error('復号できません。');
  }

  return new TextDecoder('utf-8', { fatal: true }).decode(msgBytes);
}

async function encode() {
  try {
    const password = refs.encodePassword.value;
    const message = refs.messageInput.value;
    if (!message) throw new Error('文章を入力してください。');
    if (!password) throw new Error('パスワードを入力してください。');

    setStatus('PNG生成中…');
    refs.savePngBtn.disabled = true;
    ensureTemplates();

    const { salt, cipher, messageBytes } = await createCipherFromMessage(message, password);
    const carrierBytes = buildCarrierBytes({ salt, iterations: DEFAULT_ITERATIONS, cipher });
    const layout = renderWalkPngToCanvas(refs.encodeCanvas, carrierBytes);
    generatedPngName = `zeta-trace-${new Date().toISOString().replace(/[:.]/g, '-')}.png`;
    refs.encodeInfo.textContent = `${carrierBytes.length} bytes / ${layout.cols}×${layout.rows} cells / ${refs.encodeCanvas.width}×${refs.encodeCanvas.height}px`;
    refs.savePngBtn.disabled = false;
    setStatus(`PNGを生成しました。本文 ${messageBytes.length} bytes。`, 'ok');
  } catch (err) {
    setStatus(err.message || String(err), 'error');
  }
}

function savePng() {
  if (refs.savePngBtn.disabled) return;
  refs.encodeCanvas.toBlob((blob) => {
    if (!blob) { setStatus('PNG保存に失敗しました。', 'error'); return; }
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = generatedPngName || 'zeta-trace.png';
    document.body.appendChild(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(a.href);
    setStatus('PNGを保存しました。', 'ok');
  }, 'image/png');
}

async function loadPngFile(event) {
  try {
    const file = event.target.files && event.target.files[0];
    if (!file) return;
    if (file.type && file.type !== 'image/png') throw new Error('PNGファイルを選択してください。');
    setStatus('PNG読み込み中…');
    loadedPngImageData = await imageFileToImageData(file, refs.decodeCanvas);
    refs.plainOutput.value = '';
    refs.decodeInfo.textContent = `${file.name} / ${loadedPngImageData.width}×${loadedPngImageData.height}px`;
    setStatus('PNGを読み込みました。', 'ok');
  } catch (err) {
    loadedPngImageData = null;
    refs.decodeInfo.textContent = '読み込み失敗';
    setStatus(err.message || String(err), 'error');
  } finally {
    event.target.value = '';
  }
}

async function decode() {
  try {
    const password = refs.decodePassword.value;
    if (!loadedPngImageData) throw new Error('PNGを読み込んでください。');
    if (!password) throw new Error('パスワードを入力してください。');
    setStatus('復号中…');
    refs.plainOutput.value = '';
    ensureTemplates();

    const bytes = carrierBytesFromImageData(loadedPngImageData);
    const carrier = parseCarrierBytes(bytes);
    const message = await decodeCipherToMessage(carrier.cipher, carrier.salt, carrier.iterations, password);
    refs.plainOutput.value = message;
    refs.decodeInfo.textContent = `復元 ${carrier.carrierLength} bytes / cipher ${carrier.cipher.length} bytes`;
    setStatus('復号しました。', 'ok');
  } catch (err) {
    refs.plainOutput.value = '';
    setStatus(err.message || String(err), 'error');
  }
}

async function copyText(text, okMessage) {
  if (!text) { setStatus('コピーする内容がありません。', 'error'); return; }
  try {
    await navigator.clipboard.writeText(text);
    setStatus(okMessage, 'ok');
  } catch {
    setStatus('コピーできませんでした。', 'error');
  }
}

function clearEncode() {
  refs.messageInput.value = '';
  refs.encodeInfo.textContent = '未生成';
  refs.savePngBtn.disabled = true;
  refs.encodeCanvas.width = 1;
  refs.encodeCanvas.height = 1;
  setStatus('クリアしました。');
}

function clearDecode() {
  loadedPngImageData = null;
  refs.decodeInfo.textContent = '未読み込み';
  refs.decodeCanvas.width = 1;
  refs.decodeCanvas.height = 1;
  refs.plainOutput.value = '';
  setStatus('クリアしました。');
}

function togglePassword(input, button) {
  const showing = input.type === 'text';
  input.type = showing ? 'password' : 'text';
  button.textContent = showing ? '表示' : '隠す';
}

async function cleanupOldServiceWorkers() {
  if (!('serviceWorker' in navigator)) return;
  try {
    const regs = await navigator.serviceWorker.getRegistrations();
    for (const reg of regs) await reg.unregister();
    if ('caches' in window) {
      const keys = await caches.keys();
      await Promise.all(keys.map(key => caches.delete(key)));
    }
  } catch {}
}

$('encodeBtn').addEventListener('click', encode);
$('decodeBtn').addEventListener('click', decode);
$('savePngBtn').addEventListener('click', savePng);
$('loadPngFile').addEventListener('change', loadPngFile);
$('copyPlainBtn').addEventListener('click', () => copyText(refs.plainOutput.value, 'コピーしました。'));
$('clearEncodeBtn').addEventListener('click', clearEncode);
$('clearDecodeBtn').addEventListener('click', clearDecode);
$('showEncodePassword').addEventListener('click', () => togglePassword(refs.encodePassword, $('showEncodePassword')));
$('showDecodePassword').addEventListener('click', () => togglePassword(refs.decodePassword, $('showDecodePassword')));

cleanupOldServiceWorkers();
