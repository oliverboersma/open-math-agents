#!/usr/bin/env node
// Lists open pull requests that wait for a maintainer (label needs-human-review), by problem id, into
// content/pending.json. The site shows them on the problem page and on /solved, so a proof accepted by Lean on an open
// problem is visible at once, labelled "awaiting review" (never as solved). Built at deploy time: no request at run time.
// Uses GH_TOKEN when set (CI), the public API otherwise; on any failure keeps the file already there.
import fs from "node:fs";
const REPO = "GuillaumeBAUD-coder/open-math-agents";
const OUT = new URL("../content/pending.json", import.meta.url);
const headers = { accept: "application/vnd.github+json", "user-agent": "lefttosolve-build" };
if (process.env.GH_TOKEN) headers.authorization = `Bearer ${process.env.GH_TOKEN}`;
try {
  const items = {};
  let n = 0;
  for (let page = 1; page <= 60; page++) {
    const r = await fetch(`https://api.github.com/repos/${REPO}/pulls?state=open&per_page=100&page=${page}`, { headers });
    if (!r.ok) throw new Error(`GitHub ${r.status}`);
    const prs = await r.json();
    for (const pr of prs) {
      if (!pr.labels.some((l) => l.name === "needs-human-review")) continue;
      const id = String(pr.title).trim();
      if (!/^[\w.\-]+$/.test(id) || id.length > 200) continue;
      (items[id] ??= []).push({ pr: pr.number, user: pr.user.login, at: pr.created_at.slice(0, 10) });
      n++;
    }
    if (prs.length < 100) break;
  }
  for (const v of Object.values(items)) v.sort((a, b) => a.pr - b.pr);
  fs.writeFileSync(OUT, JSON.stringify({ generated: new Date().toISOString().slice(0, 16) + "Z", items }));
  console.log(`pending.json: ${n} pull requests awaiting review, ${Object.keys(items).length} problems`);
} catch (e) {
  console.log(`pending.json kept as it is (${e.message})`);
  if (!fs.existsSync(OUT)) fs.writeFileSync(OUT, JSON.stringify({ generated: null, items: {} }));
}
