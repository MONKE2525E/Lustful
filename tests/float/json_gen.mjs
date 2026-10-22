import fs from 'node:fs';
const out = fs.openSync(process.argv[2], 'wx');
let chunk = '', count = 0;
function emit(bits) {
  if (((bits >> 52n) & 2047n) === 2047n) return;
  chunk += bits.toString(16).padStart(16, '0') + '\n'; count++;
  if (chunk.length >= 65536) { fs.writeSync(out, chunk); chunk = ''; }
}
const sign = 1n << 63n, mask = (1n << 64n) - 1n, mant = (1n << 52n) - 1n;
for (let e = 0n; e < 2047n; e++) {
  for (const m of [0n, 1n, 2n, mant, mant - 1n, mant / 2n, 0xaaaaaaaaaaaaan, 0x5555555555555n]) {
    emit((e << 52n) | m); emit(sign | (e << 52n) | m);
  }
}
const bytes = new ArrayBuffer(8), view = new DataView(bytes);
for (let e = -323; e <= 308; e++) {
  const x = Number(`1e${e}`); if (!Number.isFinite(x)) continue;
  view.setFloat64(0, x); const bits = view.getBigUint64(0);
  for (const d of [-2n,-1n,0n,1n,2n]) {
    const y = bits + d; if (y < 0n || y > mask) continue; emit(y); emit(sign | y);
  }
}
let seed = 0x7f4a7c159e3779b9n;
for (let i = 0; i < 1000000; i++) {
  seed ^= seed >> 12n; seed ^= (seed << 25n) & mask; seed ^= seed >> 27n;
  emit((seed * 2685821657736338717n) & mask);
}
if (chunk) fs.writeSync(out, chunk); fs.closeSync(out);
console.log(JSON.stringify({count, randomSeed:'7f4a7c159e3779b9', randomAttempts:1000000}));
