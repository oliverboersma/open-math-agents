#!/usr/bin/env python3
"""Answer placeholders: definitions whose body is `sorry` upstream (e.g. `def erdos_142.answer (k : ℕ) : ℕ → ℝ := sorry`)
that a problem's statement depends on. Such a problem asks for a value: it can only be solved by supplying that value
(OMA.answer) and proving the statement with the placeholder replaced by it. Writes data/placeholders.json
{problem id: [fully qualified placeholder names, in order of appearance in the statement]}."""
import json, gzip, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
fc = json.load(gzip.open(os.path.join(HERE, "..", "data", "fc_files.json.gz")))
cat = json.load(open(os.path.join(HERE, "..", "data", "catalog.json"), encoding="utf-8"))["problems"]
START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|public)\s+)*(def|abbrev|opaque|theorem|lemma|instance|structure|inductive|class|axiom|namespace|end|section)\b", re.M)

def placeholders(src):
    """(fully qualified name, short name) of every sorry-valued def/abbrev/opaque, with its namespace."""
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
    src = re.sub(r"--[^\n]*", "", src)
    idx = [m.start() for m in START.finditer(src)] + [len(src)]
    ns, out = [], []
    for a, b in zip(idx, idx[1:]):
        chunk = src[a:b]
        kw = START.match(chunk).group(1)
        if kw == "namespace":
            ns.append(chunk.split()[1]); continue
        if kw == "end":
            parts = chunk.split()
            if len(parts) > 1 and ns and parts[1] == ns[-1]: ns.pop()
            continue
        if kw not in ("def", "abbrev", "opaque"): continue
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|public)\s+)*\w+\s+([^\s(:{\[]+)", chunk)
        if not m or ":=" not in chunk: continue
        body = chunk.split(":=", 1)[1].strip()
        if re.fullmatch(r"(by\s+)?sorry|answer\(sorry\)", body):
            name = m.group(1)
            out.append((".".join(ns + [name]), name))
    return out

res = {}
for p in cat:
    ph = placeholders(fc.get(p.get("file") or "", ""))
    lean = p.get("lean") or ""
    used = []
    for full, short in ph:
        pos = [m.start() for m in re.finditer(r"(?<![\w.])(" + re.escape(full) + "|" + re.escape(short) + r")(?![\w])", lean)]
        if pos: used.append((min(pos), full))
    if used: res[p["id"]] = [f for _, f in sorted(used)]
json.dump(res, open(os.path.join(HERE, "..", "data", "placeholders.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=0, sort_keys=True)
print(len(res), "problems ask for a value;", sum(len(v) > 1 for v in res.values()), "with several placeholders")
