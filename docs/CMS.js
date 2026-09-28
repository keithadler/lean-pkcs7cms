import * as React from 'react';
const e = React.createElement;

// Every fact on this panel arrives from Lean (CMS.Widget.widgetProps): the parsed DER tree, the signed
// attributes, each rule of SignerValid, the RSA block sᵉ mod n, and the TSTInfo that was signed. The
// JavaScript only lays them out.

const BG = '#0b0d12', PANEL = '#12151c', LINE = '#262c3a', INK = '#e8eaf0', DIM = '#8a90a2', FAINT = '#4a5163';
const GREEN = '#5fd4a0', RED = '#ff7a7a', AMBER = '#f2b35e', BLUE = '#7fb2ff', VIOLET = '#c29bff', TEAL = '#5cc8d6';
const MONO = "'JetBrains Mono', ui-monospace, 'SF Mono', Menlo, Consolas, monospace";
const SANS = "Inter, -apple-system, 'Segoe UI', Helvetica, Arial, sans-serif";

const bytes = h => { const a = []; for (let i = 0; i < h.length; i += 2) a.push(h.slice(i, i + 2)); return a; };
const when = n => { const s = String(n); return `${s.slice(0, 4)}-${s.slice(4, 6)}-${s.slice(6, 8)} ${s.slice(8, 10)}:${s.slice(10, 12)}:${s.slice(12, 14)} UTC`; };

const ATTRS = {
  '2a864886f70d010903': 'content-type', '2a864886f70d010904': 'message-digest', '2a864886f70d010905': 'signing-time',
  '2a864886f70d010906': 'countersignature', '2a864886f70d010910020c': 'signing-certificate',
  '2a864886f70d010910022f': 'signing-certificate-v2',
};
const TYPES = { '2a864886f70d010701': 'id-data', '2a864886f70d0109100104': 'TSTInfo (RFC 3161)' };

// Offsets of every node, from the header and content lengths Lean reports.
function walk(node, off = 0, path = [], out = {}) {
  out[path.join('.')] = { off, hdr: node.h, len: node.n, tag: node.t };
  if (node.c) { let o = off + node.h; node.c.forEach((k, i) => { walk(k, o, path.concat(i), out); o += k.h + k.n; }); }
  return out;
}

function Panel({ title, sub, children, style }) {
  return e('div', { style: { background: PANEL, border: `1px solid ${LINE}`, borderRadius: 14, padding: '14px 16px', ...style } },
    e('div', { style: { display: 'flex', alignItems: 'baseline', gap: 10, marginBottom: 10 } },
      e('div', { style: { fontSize: 11.5, fontWeight: 700, letterSpacing: '.08em', textTransform: 'uppercase', color: BLUE } }, title),
      sub ? e('div', { style: { fontSize: 11.5, color: DIM } }, sub) : null),
    children);
}

const Thm = ({ n }) => e('span', { style: { fontFamily: MONO, fontSize: 11.5, color: GREEN } }, n);

// The whole message as a bar: where the content, the certificates and the signer sit.
function ByteMap({ tree, size }) {
  const w = walk(tree);
  const kids = tree.c[1].c[0].c;
  const certIdx = kids.findIndex(k => k.t === 0xa0);
  const siPath = `1.0.${kids.length - 1}.0`;
  const cats = [];
  const seg = (key, color) => w[key] ? { ...w[key], color } : null;
  const content = seg('1.0.2', TEAL);
  const certs = certIdx >= 0 ? kids[certIdx].c.map((_, i) => seg(`1.0.${certIdx}.${i}`, i % 2 ? '#3d4a66' : '#56688f')) : [];
  const sik = kids[kids.length - 1].c[0].c;
  const attrs = seg(`${siPath}.${sik.findIndex(k => k.t === 0xa0)}`, AMBER);
  const sig = seg(`${siPath}.${sik.findIndex(k => k.t === 0x04)}`, VIOLET);
  const segs = [content, ...certs, attrs, sig].filter(Boolean);
  const len = s => s.hdr + s.len;
  if (content) cats.push({ color: TEAL, label: 'encapsulated content (TSTInfo)', n: len(content) });
  if (certs.length) cats.push({ color: '#56688f', label: `${certs.length} certificates`, n: certs.reduce((a, s) => a + len(s), 0) });
  if (attrs) cats.push({ color: AMBER, label: 'signed attributes', n: len(attrs) });
  if (sig) cats.push({ color: VIOLET, label: 'RSA signature', n: sig.len });
  const W = 1000, H = 30;
  const x = o => (o / size) * W;
  return e('div', null,
    e('svg', { viewBox: `0 0 ${W} ${H}`, style: { width: '100%', display: 'block' } },
      e('rect', { x: 0, y: 0, width: W, height: H, rx: 6, fill: '#1a1f2b' }),
      segs.map((s, i) => e('rect', { key: i, x: x(s.off) + 0.5, y: 0, width: Math.max(2, x(len(s)) - 1), height: H, fill: s.color, rx: 3 }))),
    e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: '4px 16px', marginTop: 8, fontSize: 12.5 } },
      cats.map((c, i) => e('div', { key: i, style: { display: 'flex', alignItems: 'center', gap: 6 } },
        e('span', { style: { width: 10, height: 10, borderRadius: 2, background: c.color, display: 'inline-block' } }),
        e('span', { style: { color: INK } }, c.label), e('span', { style: { color: DIM } }, `${c.n.toLocaleString()} B`)))),
    e('div', { style: { fontSize: 12, color: DIM, marginTop: 6 } }, `${size.toLocaleString()} bytes, parsed by lean-x509's DER parser`, ' · ', e(Thm, { n: 'decode_der' })));
}

function TagSwap({ written, signed, signedLen }) {
  const row = (label, h, hi) => e('div', { style: { display: 'flex', alignItems: 'center', gap: 12, margin: '4px 0' } },
    e('div', { style: { width: 128, fontSize: 12.5, color: DIM } }, label),
    e('div', { style: { fontFamily: MONO, fontSize: 17, letterSpacing: '.04em' } },
      bytes(h).map((b, i) => e('span', { key: i, style: { color: i === 0 ? hi : INK, fontWeight: i === 0 ? 800 : 500, marginRight: 8 } }, b)),
      e('span', { style: { color: FAINT } }, '…')));
  return e('div', null,
    row('in the message', written, AMBER),
    row('what is signed', signed, GREEN),
    e('div', { style: { fontSize: 12, color: DIM, marginTop: 6 } },
      `${signedLen} bytes: the same bytes, one tag changed from [0] IMPLICIT to SET OF (RFC 5652 §5.4)`, ' · ', e(Thm, { n: 'signed_attrs_slice' })));
}

function Attrs({ attrs, contentHash, eContentType }) {
  return e('div', { style: { display: 'grid', gridTemplateColumns: 'auto 1fr', columnGap: 14, rowGap: 5, fontSize: 13 } },
    attrs.flatMap((a, i) => {
      const name = ATTRS[a.oid] || a.oid;
      let v = '', ok = null;
      if (name === 'content-type') { const t = a.values[0].slice(4); v = TYPES[t] || t; ok = t === eContentType; }
      else if (name === 'message-digest') { v = a.values[0].slice(4, 20) + '…'; ok = a.values[0].slice(4) === contentHash; }
      else if (name === 'signing-time') { const s = a.values[0]; v = bytes(s.slice(4)).map(b => String.fromCharCode(parseInt(b, 16))).join(''); }
      else v = `${a.values.length} value`;
      return [
        e('div', { key: 'n' + i, style: { fontFamily: MONO, color: INK } }, name),
        e('div', { key: 'v' + i, style: { color: DIM, fontFamily: MONO } }, v,
          ok === true ? e('span', { style: { color: GREEN, marginLeft: 8, fontFamily: SANS } },
            name === 'message-digest' ? '= SHA-256 of the content' : "= the content's type") : null)];
    }));
}

// The 512 bytes RSA reveals, as Lean computed them: sᵉ mod n.
function Block({ block, expected, bits, e: ex }) {
  const bs = bytes(block);
  const n = bs.length, cols = 32;
  const sep = bs.indexOf('00', 2);
  const colorOf = i => i < 2 ? BLUE : i < sep ? '#3a4152' : i === sep ? BLUE : i < n - 32 ? VIOLET : GREEN;
  const cell = 9, gap = 2, rows = Math.ceil(n / cols);
  const W = cols * (cell + gap), H = rows * (cell + gap);
  return e('div', null,
    e('div', { style: { display: 'flex', gap: 16, alignItems: 'flex-start' } },
      e('svg', { viewBox: `0 0 ${W} ${H}`, style: { width: 330, flex: '0 0 330px', display: 'block' } },
        bs.map((b, i) => e('rect', { key: i, x: (i % cols) * (cell + gap), y: Math.floor(i / cols) * (cell + gap), width: cell, height: cell, rx: 1.5, fill: colorOf(i) }))),
      e('div', { style: { fontSize: 12.5, color: DIM, lineHeight: 1.7 } },
        e('div', null, e('span', { style: { color: BLUE, fontFamily: MONO } }, '00 01'), '  start'),
        e('div', null, e('span', { style: { color: '#6a7390', fontFamily: MONO } }, 'FF … FF'), `  ${sep - 2} bytes of padding`),
        e('div', null, e('span', { style: { color: BLUE, fontFamily: MONO } }, '00'), '  end of padding'),
        e('div', null, e('span', { style: { color: VIOLET, fontFamily: MONO } }, '30 31 … 04 20'), '  DigestInfo, SHA-256'),
        e('div', null, e('span', { style: { color: GREEN, fontFamily: MONO } }, bs.slice(n - 32, n - 28).join(' ') + ' …'), '  SHA-256 of the signed bytes'),
        e('div', { style: { marginTop: 8, color: block === expected ? GREEN : RED, fontWeight: 700, fontFamily: SANS } },
          block === expected ? `= the expected block, all ${n} bytes` : 'differs from the expected block'),
        e('div', null, `${bits}-bit modulus, e = ${ex}`, ' · ', e(Thm, { n: 'verify_iff' })))));
}

function Checks({ checks }) {
  return e('div', null, checks.map((c, i) => e('div', { key: i, style: { display: 'flex', gap: 10, alignItems: 'baseline', padding: '5px 0', borderTop: i ? `1px solid ${LINE}` : 'none' } },
    e('span', { style: { color: c.ok ? GREEN : RED, fontWeight: 800, width: 14 } }, c.ok ? '✓' : '✗'),
    e('span', { style: { flex: 1, fontSize: 13.5, color: INK } }, c.rule),
    e('span', { style: { fontSize: 11.5, color: DIM, whiteSpace: 'nowrap' } }, c.source),
    e('span', { style: { width: 128, textAlign: 'right' } }, e(Thm, { n: c.thm })))));
}

export default function CMSWidget(p) {
  if (!p || !p.tree) return e('div', { style: { color: RED } }, 'The message did not decode.');
  return e('div', { style: { background: BG, color: INK, fontFamily: SANS, padding: 18, borderRadius: 16, display: 'flex', flexDirection: 'column', gap: 12 } },
    e('div', { style: { display: 'flex', alignItems: 'center', gap: 16, flexWrap: 'wrap' } },
      e('div', { style: { background: p.valid ? 'rgba(95,212,160,.14)' : 'rgba(255,122,122,.14)', color: p.valid ? GREEN : RED, fontWeight: 800, fontSize: 15, padding: '7px 14px', borderRadius: 9, letterSpacing: '.03em' } },
        p.valid ? '✓ VALID, CHECKED BY LEAN' : '✗ NOT VALID'),
      e('div', { style: { fontSize: 21, fontWeight: 800 } }, p.title),
      e('div', { style: { fontSize: 13, color: DIM } }, `signed by ${p.signer} · ${p.bits}-bit RSA`)),
    e('div', { style: { display: 'flex', gap: 12, flexWrap: 'wrap' } },
      e('div', { style: { flex: '1 1 560px', display: 'flex', flexDirection: 'column', gap: 12, minWidth: 0 } },
        e(Panel, { title: 'The message', sub: 'CMS SignedData, RFC 5652' }, e(ByteMap, { tree: p.tree, size: p.size })),
        e(Panel, { title: 'The signed bytes', sub: 'the signature covers the attributes, the attributes cover the content' },
          e(TagSwap, p), e('div', { style: { height: 10 } }), e(Attrs, p)),
        e(Panel, { title: 'sᵉ mod n', sub: 'the block RSA reveals, computed by Lean' }, e(Block, p))),
      e('div', { style: { flex: '1 1 430px', display: 'flex', flexDirection: 'column', gap: 12, minWidth: 0 } },
        e(Panel, { title: 'SignerValid, rule by rule', sub: 'the checker is this specification: signerOk_iff' }, e(Checks, p)),
        e(Panel, { title: 'What was signed', sub: 'the TSTInfo inside the token' },
          e('div', { style: { fontSize: 13, color: DIM } }, 'DigiCert says this SHA-256 existed at'),
          e('div', { style: { fontSize: 19, fontWeight: 800, margin: '4px 0 8px' } }, when(p.stampTime)),
          e('div', { style: { fontFamily: MONO, fontSize: 13.5, color: INK, wordBreak: 'break-all', lineHeight: 1.5 } }, p.stampHash),
          e('div', { style: { fontSize: 12, color: DIM, marginTop: 8 } }, 'the sealed findings file · ', e(Thm, { n: 'findings_stamped' }), ', by ', e('span', { style: { fontFamily: MONO, color: GREEN } }, 'decide +kernel'))))),
    e('div', { style: { fontSize: 11.5, color: FAINT } }, 'Every value on this panel is computed by Lean from the definitions the theorems are about (CMS.Widget.widgetProps). github.com/keithadler/lean-pkcs7cms'));
}
