#!/usr/bin/env node
// Load data/gen/catalog.sql into the catalogue D1 database, in batches (D1 caps one statement at 100 KB and one
// request at a few MB).
//   local (vite dev / preview running): node scripts/seed_d1.mjs --local http://localhost:3124
//   remote (Cloudflare D1 import API; CLOUDFLARE_API_TOKEN, or a token injected by the network proxy):
//     node scripts/seed_d1.mjs --remote <account_id> <database_id> [--if-changed]
//   --if-changed skips the import when the remote meta.version already equals data/gen/version.txt.
import fs from "node:fs";
import crypto from "node:crypto";

const [mode, a, b] = process.argv.slice(2);
// --part mo loads data/gen/catalog-mo.sql (MathOverflow tables, version key version_mo); default: data/gen/catalog.sql.
const part = process.argv.includes("--part") ? process.argv[process.argv.indexOf("--part") + 1] : "core";
const sqlFile = part === "mo" ? "catalog-mo.sql" : "catalog.sql";
const versionFile = part === "mo" ? "version-mo.txt" : "version.txt";
const versionKey = part === "mo" ? "version_mo" : "version";
const sql = fs.readFileSync(new URL(`../data/gen/${sqlFile}`, import.meta.url), "utf8");

// Split on ";" outside single-quoted strings ('' is an escaped quote and toggles twice).
const stmts = [];
let start = 0, inq = false;
for (let i = 0; i < sql.length; i++) {
  const c = sql[i];
  if (c === "'") inq = !inq;
  else if (c === ";" && !inq) { const s = sql.slice(start, i + 1).trim(); if (s) stmts.push(s); start = i + 1; }
}

const token = process.env.CLOUDFLARE_API_TOKEN && process.env.CLOUDFLARE_API_TOKEN !== "proxy-injected" ? process.env.CLOUDFLARE_API_TOKEN : "proxy-injected";

if (mode === "--remote") {
  const api = `https://api.cloudflare.com/client/v4/accounts/${a}/d1/database/${b}`;
  const call = async (path, body) => {
    const r = await fetch(api + path, { method: "POST", headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" }, body: JSON.stringify(body) });
    const j = await r.json().catch(() => ({}));
    if (!r.ok || j.success === false) throw new Error(`${path} HTTP ${r.status} ${JSON.stringify(j.errors ?? j).slice(0, 300)}`);
    return j.result;
  };
  const version = fs.readFileSync(new URL(`../data/gen/${versionFile}`, import.meta.url), "utf8").trim();
  if (process.argv.includes("--if-changed")) {
    const cur = await call("/query", { sql: `SELECT v FROM meta WHERE k = '${versionKey}'` }).then((r) => r[0].results[0]?.v).catch(() => null);
    if (cur === version) { console.log(`remote D1 already at ${version}: nothing to import`); process.exit(0); }
    console.log(`remote D1 at ${cur ?? "(empty)"}, importing ${version}`);
  }
  const etag = crypto.createHash("md5").update(sql).digest("hex");
  const init = await call("/import", { action: "init", etag });
  // No upload URL: D1 already holds a file with this etag (an earlier import of the same SQL); ingest it again.
  if (init.upload_url) {
    const up = await fetch(init.upload_url, { method: "PUT", body: sql });
    if (!up.ok) throw new Error(`upload HTTP ${up.status}`);
  }
  let st = await call("/import", { action: "ingest", etag, filename: init.filename });
  let bookmark = st.at_bookmark;
  for (let i = 0; st.status !== "complete" && st.status !== "error" && i < 200; i++) {
    await new Promise((res) => setTimeout(res, 3000));
    if (!bookmark) {
      // Some ingest/poll answers carry no bookmark (large files): then watch the version row the SQL writes last.
      const v = await call("/query", { sql: `SELECT v FROM meta WHERE k = '${versionKey}'` }).then((r) => r[0].results[0]?.v).catch(() => null);
      if (v === version) { st = { status: "complete", result: { num_queries: "?" } }; break; }
      continue;
    }
    st = await call("/import", { action: "poll", current_bookmark: bookmark });
    if (/not currently importing/i.test(`${st.error ?? ""} ${JSON.stringify(st.messages ?? "")}`)) break;
    bookmark = st.at_bookmark ?? bookmark;
  }
  // "Not currently importing anything": the import already finished between two polls. Trust the version row.
  if (st.status !== "complete") {
    const v = await call("/query", { sql: `SELECT v FROM meta WHERE k = '${versionKey}'` }).then((r) => r[0].results[0]?.v).catch(() => null);
    if (v === version) st = { status: "complete", result: { num_queries: "?" } };
  }
  if (st.status !== "complete") throw new Error(`import ${st.status}: ${st.error ?? JSON.stringify(st.messages)}`);
  console.log(`imported ${st.result?.num_queries ?? "?"} statements into remote D1 (${version}); rows written: ${st.result?.meta?.rows_written ?? "?"}`);
  process.exit(0);
}

let url, headers = { "Content-Type": "application/json" };
if (mode === "--local") {
  const base = (a ?? "http://localhost:3124").replace(/\/$/, "") + "/cdn-cgi/local/explorer/api";
  const dbs = await (await fetch(`${base}/d1/database`)).json();
  const list = dbs.result ?? dbs;
  const db = list.find((d) => /catalog/i.test(d.name ?? d.binding ?? "")) ?? list[0];
  if (!db) throw new Error("no local D1 database: start vite dev or preview first");
  url = `${base}/d1/database/${db.uuid ?? db.id ?? db.database_id}/raw`;
} else {
  console.error("usage: seed_d1.mjs --local [base] | --remote <account_id> <database_id> [--if-changed]");
  process.exit(2);
}
const MAX = 90_000; // bytes of SQL per request: the whole batch counts against the 100 KB limit
let batch = [], size = 0, done = 0;
async function flush() {
  if (!batch.length) return;
  for (let attempt = 1; ; attempt++) {
    const r = await fetch(url, { method: "POST", headers, body: JSON.stringify({ sql: batch.join("\n") }) });
    const j = await r.json().catch(() => ({}));
    if (r.ok && j.success !== false) break;
    if (attempt >= 4) throw new Error(`batch at ${done}: HTTP ${r.status} ${JSON.stringify(j.errors ?? j).slice(0, 400)}`);
    await new Promise((res) => setTimeout(res, 1000 * attempt));
  }
  done += batch.length; batch = []; size = 0;
  if (done % 5000 < batch.length || done === stmts.length) console.log(`${done}/${stmts.length} statements`);
}
for (const s of stmts) {
  const n = Buffer.byteLength(s); if (size + n > MAX) await flush();
  batch.push(s); size += n + 1;
}
await flush();
console.log(`loaded ${stmts.length} statements (${sqlFile}) into local D1`);
