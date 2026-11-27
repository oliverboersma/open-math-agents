#!/usr/bin/env python3
"""Static gate for a submitted file, run BEFORE anything compiles (locally and in CI).

Usage (from the repository root): python3 -I tools/lint.py <file> data/catalog.json
Prints JSON {ok, type, problem, ..., errors}. Exit code 0 only if ok.

Four kinds of file:
  proofs/<problem id>.lean      proves (or refutes) a catalogue problem: OMA.solution / OMA.disproof
  proofs/<X>.R<n>.H<k>.lean     proves step H<k> of the merged reduction reductions/<X>.R<n>.lean
  reductions/<X>.R<n>.lean      splits X (a problem or a step) into 2 to 4 hypotheses H1..Hk with H1 → … → Hk → X
  statements/<id>.lean          states, for the first time, a problem that had no Lean statement (data/extra.json);
                                compiles with exactly one sorry (the body of main); merged only after human review

Why so strict: Lean can run arbitrary code while it compiles (#eval, macros, elab, initialize, run_tac ...).
A submission must not be able to touch the CI runner or forge its own verdict, so everything that could
execute code at compile time is refused outright. Keep the naming rules identical to lib/steps.ts.
"""
import json
import os
import re
import sys

path, catalog_path = sys.argv[1], sys.argv[2]
rel = os.path.relpath(path).replace(os.sep, "/")
errors = []
out = {"file": rel}

cat = json.load(open(catalog_path, encoding="utf-8"))
PROBLEMS = {p["id"]: p for p in cat["problems"]}
# formal-conjectures can lag behind erdosproblems.com: a main statement (not a variant) still tagged "research open"
# whose Erdős problem is proved, disproved or solved is a known result. Same rule in scripts/build_data.mjs.
for _p in PROBLEMS.values():
    if _p["kind"] == "open" and re.match(r"(proved|disproved|solved)\b", _p.get("erdosState") or "") and not re.search(r"\.variants?\.", _p["id"]):
        _p["kind"] = "known"
_extra_path = os.path.join(os.path.dirname(os.path.abspath(catalog_path)), "extra.json")
EXTRA = {p["id"]: p for p in json.load(open(_extra_path, encoding="utf-8"))["problems"]} if os.path.exists(_extra_path) else {}
# The long tail waits for statements too: OEIS / MathOverflow / Math.SE / curated (extra2.json) and the MathOverflow
# dump (extra3.json.gz). Only their ids matter here.
_data_dir = os.path.dirname(os.path.abspath(catalog_path))
if os.path.exists(os.path.join(_data_dir, "extra2.json")):
    for _r in json.load(open(os.path.join(_data_dir, "extra2.json"), encoding="utf-8"))["rows"]:
        EXTRA.setdefault(_r[0], {"id": _r[0]})
if os.path.exists(os.path.join(_data_dir, "extra3.json.gz")):
    import gzip
    for _r in json.load(gzip.open(os.path.join(_data_dir, "extra3.json.gz"), "rt", encoding="utf-8"))["rows"]:
        EXTRA.setdefault(f"mo-{_r[0]}", {"id": f"mo-{_r[0]}"})
STEP_RE = re.compile(r"^(.+)\.R(\d{1,2})\.H([1-4])$")


def san(rid):
    return "R_" + re.sub(r"[^A-Za-z0-9]", "_", rid)


def module_of(rid):
    return "OMAReductions." + san(rid)


def ns_of(rid):
    return "OMA." + san(rid)


def ssan(pid):
    return "S_" + re.sub(r"[^A-Za-z0-9]", "_", pid)


def strip_comments(s):
    res, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
            continue
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and s.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            res.append(s[i])
        i += 1
    if depth:
        errors.append("unterminated block comment")
    return "".join(res)


def hypotheses(code):
    """H1..Hk definitions of a reduction file, in order."""
    found = {}
    for m in re.finditer(r"^def\s+H([1-9])\s*:\s*Prop\s*:=\s*(.*?)(?=^\s*(?:def|theorem|lemma|end|namespace|open|section|variable|@\[)\b|\Z)",
                         code, re.S | re.M):
        found[int(m.group(1))] = m.group(2).strip()
    return found


def read_code(p):
    raw = open(p, "rb").read()
    return strip_comments(raw.decode("utf-8", "replace"))


def describe_target(tid):
    """What a reduction or a step may target: a catalogue problem, or a step of a merged reduction."""
    if tid in PROBLEMS:
        p = PROBLEMS[tid]
        return {"kind": p["kind"], "import": p["module"], "statement": f"type_of% @{p['decl']}", "decl": p["decl"]}
    if tid in EXTRA:
        # provable only once its statement is merged
        if not os.path.exists(f"statements/{tid}.lean"):
            return None
        decl = f"OMA.{ssan(tid)}.main"
        return {"kind": "open", "import": f"OMAStatements.{ssan(tid)}", "statement": f"type_of% @{decl}", "decl": decl}
    m = STEP_RE.match(tid)
    if m:
        rid = f"{m.group(1)}.R{m.group(2)}"
        rfile = f"reductions/{rid}.lean"
        if not os.path.exists(rfile):
            return None
        hs = hypotheses(read_code(rfile))
        k = int(m.group(3))
        if k not in hs:
            return None
        root = describe_target(m.group(1))
        return {"kind": root["kind"] if root else "step", "import": module_of(rid), "statement": f"{ns_of(rid)}.H{k}", "decl": None,
                "reduction": rid}
    return None


# ---- which kind of file ------------------------------------------------------------------------
ms = re.fullmatch(r"statements/([A-Za-z0-9_.'\-]+)\.lean", rel)
mp = re.fullmatch(r"proofs/([A-Za-z0-9_.'\-]+)\.lean", rel)
mr = re.fullmatch(r"reductions/([A-Za-z0-9_.'\-]+)\.R(\d{1,2})\.lean", rel)
if ms:
    pid = ms.group(1)
    ftype = "statement"
    target = {"kind": "statement", "import": "Mathlib", "statement": "", "decl": None}
    if pid not in EXTRA:
        errors.append(f"{pid} is not a problem waiting for a statement")
elif mp:
    pid = mp.group(1)
    target = describe_target(pid)
    ftype = "proof" if (pid in PROBLEMS or pid in EXTRA) else "step"
    if target is None:
        if pid in EXTRA:
            errors.append(f"{pid} has no Lean statement yet: send statements/{pid}.lean first (it must be reviewed and merged)")
        else:
            errors.append(f"unknown problem or step id {pid} (a step needs its reduction merged first)")
elif mr:
    pid = f"{mr.group(1)}.R{mr.group(2)}"
    ftype = "reduction"
    target = describe_target(mr.group(1))
    if not 1 <= int(mr.group(2)) <= 99:
        errors.append("reduction number must be 1..99")
    if target is None:
        errors.append(f"unknown reduction target {mr.group(1)}")
else:
    print(json.dumps({"ok": False, "file": rel, "errors": ["file must be proofs/<id>.lean, reductions/<id>.R<n>.lean or statements/<id>.lean (letters, digits, _ . ' - only)"]}))
    sys.exit(1)

out.update(type=ftype, problem=pid)
if errors:
    out.update(ok=False, errors=errors)
    print(json.dumps(out, ensure_ascii=False))
    sys.exit(1)

raw = open(path, "rb").read()
if len(raw) > 512 * 1024:
    errors.append("file larger than 512 KiB")
try:
    src = raw.decode("utf-8")
except UnicodeDecodeError:
    src = ""
    errors.append("file is not UTF-8")
code = strip_comments(src)

# ---- rules shared by every file ----------------------------------------------------------------
if '"' in code:
    errors.append("no double-quote characters (string literals) allowed")
if "\u0000" in code:
    errors.append("NUL byte")

BANNED = [
    r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\baxioms\b", r"\bnative_decide\b", r"\bunsafe\b", r"\bpartial\b",
    r"\bopaque\b", r"\bimplemented_by\b", r"\bextern\b", r"\bmacro\w*", r"\bsyntax\w*", r"\belab\w*", r"\bnotation\w*",
    r"\binfix[lr]?\b", r"\bprefix\b", r"\bpostfix\b", r"\binitialize\b", r"\bbuiltin_initialize\b", r"\brun_cmd\b",
    r"\brun_tac\b", r"\brun_elab\b", r"\bby_elab\b", r"\battribute\b", r"\bdeclare_\w+", r"\bmeta\b", r"\bIO\b",
    r"\bLean\.(Elab|Meta|Compiler|Environment|IR|ofReduceBool|trustCompiler)", r"\bdecide\s*:=\s*true", r"\bimport\s+Lean\b",
    r"#(eval|print|check|reduce|exit|guard|help|lint|find|synth|where|show|time|output|widget|html|norm_num|simp|conv|"
    r"parse|test|explode|long_names|search|loogle|leansearch|moogle|import|min_imports|unused|sample|allow|define|stop|"
    r"count_heartbeats|adaptation_note|align|mathlib|tactic|kernel|compile|leanchecker|version|guard_msgs|trans|redundant)\w*",
]
if ftype == "statement":
    BANNED = [b for b in BANNED if b != r"\bsorry\b"]
for pat in BANNED:
    m = re.search(pat, code)
    if m:
        errors.append(f"forbidden: {m.group(0)!r}")

for m in re.finditer(r"@\[([^\]]*)\]", code):
    if m.group(1).strip() not in ("simp", "local simp"):
        errors.append(f"attribute @[{m.group(1)}] not allowed (only @[simp], @[local simp])")

for m in re.finditer(r"\bset_option\s+([\w.]+)\s+(\S+)(\s+in\b)?", code):
    name, val, has_in = m.group(1), m.group(2), m.group(3)
    if name not in ("maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats", "synthInstance.maxSize") or not val.isdigit() or not has_in:
        errors.append(f"set_option {name} {val} not allowed (only numeric maxHeartbeats/maxRecDepth/synthInstance.* with `in`)")

lines = [l for l in code.splitlines() if l.strip()]
imports = [l.strip() for l in lines if re.match(r"\s*import\b", l)]
want_import = f"import {target['import']}"
if ftype == "statement":
    if not imports or not re.fullmatch(r"import Mathlib(\.[A-Za-z0-9_]+)*", imports[0]):
        errors.append("a statement imports Mathlib only (first line: import Mathlib, or Mathlib modules)")
elif not imports or imports[0] != want_import:
    errors.append(f"first line must be: {want_import}")
for l in imports[1:]:
    if not re.fullmatch(r"import Mathlib(\.[A-Za-z0-9_]+)*", l):
        errors.append(f"only Mathlib imports may follow the first import: {l!r}")
body_started = False
for l in lines:
    if re.match(r"\s*import\b", l):
        if body_started:
            errors.append("imports must come first")
            break
    else:
        body_started = True

if target.get("decl"):
    d = re.escape(target["decl"])
    if re.search(r"(?<![\w.])" + d + r"(?![\w.])", re.sub(r"type_of%\s*@" + d, "", code)):
        errors.append(f"the file must not use the upstream declaration {target['decl']} itself")

# ---- per kind ----------------------------------------------------------------------------------
polarity, theorem = "proof", None
# Problems that ask for a value: the statement depends on a placeholder defined as `sorry` upstream
# (data/placeholders.json). They are solved by supplying the value, OMA.answer, and proving the statement once the
# placeholder is replaced by it: `theorem OMA.solution : <placeholder> = OMA.answer → type_of% @<decl> := ...`.
# The axiom audit then skips the placeholder's value only (tools/check.sh); a person checks that the answer is a real
# answer (explicit, not a restatement of the question).
_PH_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "placeholders.json")
PLACEHOLDERS = json.load(open(_PH_FILE, encoding="utf-8")) if os.path.exists(_PH_FILE) else {}
ph = PLACEHOLDERS.get(pid, []) if ftype == "proof" else []
if ph:
    d = re.escape(target["decl"]); a = re.escape(ph[0])
    sol = re.findall(r"\btheorem\s+OMA\.solution\s*:\s*" + a + r"\s*=\s*OMA\.answer\s*→\s*type_of%\s*@" + d + r"\s*:=", code)
    if len(sol) != 1 or len(re.findall(r"\bOMA\.(solution|disproof)\b", code)) != 1:
        errors.append(f"this problem asks for a value: the file must contain exactly one `theorem OMA.solution : {ph[0]} = OMA.answer → type_of% @{target['decl']} := ...` (and no OMA.disproof)")
    defs = re.findall(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+OMA\.answer\b(.*?)(?=^\S|\Z)", code, re.M | re.S)
    if len(defs) != 1:
        errors.append("define the value exactly once: `def OMA.answer : <same type as the placeholder> := <explicit value>`")
    else:
        body = defs[0]
        top = target["decl"].split(".")[0]
        if re.search(r"(?<![\w.])" + re.escape(top) + r"\.", body) or re.search(r"^\s*(open|namespace)\s+[^\n]*\b" + re.escape(top) + r"\b", code, re.M):
            errors.append(f"OMA.answer may not use the problem's own definitions ({top}.…): give the value itself, not a restatement of the question")
        if re.search(re.escape(ph[0].split(".")[-2] + "." + ph[0].split(".")[-1]) if "." in ph[0] else re.escape(ph[0]), body):
            errors.append("OMA.answer may not mention the placeholder")
        if re.search(r"\b(Classical\.choose|Exists\.choose|Classical\.epsilon|Classical\.indefiniteDescription|Nat\.find|sInf|sSup|iInf|iSup|Function\.invFun|limUnder|choose)\b|[⨅⨆]", body):
            errors.append("OMA.answer must be an explicit value: no choice, infimum/supremum or limit of the very quantity asked for")
    polarity, theorem = "proof", "OMA.solution"
    out["skipAxiomsOf"] = ph
elif ftype == "proof":
    d = re.escape(target["decl"])
    proof = re.findall(r"\btheorem\s+OMA\.solution\s*:\s*type_of%\s*@" + d + r"\s*:=", code)
    disproof = re.findall(r"\btheorem\s+OMA\.disproof\s*:\s*¬\s*\(\s*type_of%\s*@" + d + r"\s*\)\s*:=", code)
    if len(proof) + len(disproof) != 1 or len(re.findall(r"\bOMA\.(solution|disproof)\b", code)) != 1:
        errors.append(f"must contain exactly one `theorem OMA.solution : type_of% @{target['decl']} := ...` "
                      f"or `theorem OMA.disproof : ¬ (type_of% @{target['decl']}) := ...`, and no other mention of them")
    polarity = "disproof" if disproof else "proof"
    theorem = "OMA." + ("disproof" if disproof else "solution")
elif ftype == "step":
    st = re.escape(target["statement"])
    if len(re.findall(r"\btheorem\s+OMA\.solution\s*:\s*" + st + r"\s*:=", code)) != 1 or len(re.findall(r"\bOMA\.solution\b", code)) != 1:
        errors.append(f"must contain exactly one `theorem OMA.solution : {target['statement']} := ...`")
    theorem = "OMA.solution"
elif ftype == "statement":
    ns = f"OMA.{ssan(pid)}"
    if not re.search(r"^namespace\s+" + re.escape(ns) + r"\s*$", code, re.M) or not re.search(r"^end\s+" + re.escape(ns) + r"\s*$", code, re.M):
        errors.append(f"the file must open `namespace {ns}` and close it with `end {ns}`")
    mains = re.findall(r"\btheorem\s+main\s*:(.*?):=\s*(by\s+sorry|sorry)\b", code, re.S)
    if len(mains) != 1 or len(re.findall(r"\btheorem\s+main\b", code)) != 1:
        errors.append("must contain exactly one `theorem main : <the statement> := by sorry`")
    elif re.fullmatch(r"\s*(sorry|True|False)\s*", mains[0][0]):
        errors.append("the statement of main is a placeholder: state the actual problem")
    if len(re.findall(r"\bsorry\b", code)) != 1:
        errors.append("exactly one sorry is allowed: the body of main (definitions must be complete)")
    if re.search(r"\b(theorem|lemma)\s+(?!main\b)\S+", code):
        errors.append("only `theorem main` may be declared as a theorem (put no proofs in a statement file)")
    theorem = f"{ns}.main"
    out["module"] = f"OMAStatements.{ssan(pid)}"
else:  # reduction
    ns = ns_of(pid)
    if not re.search(r"^namespace\s+" + re.escape(ns) + r"\s*$", code, re.M) or not re.search(r"^end\s+" + re.escape(ns) + r"\s*$", code, re.M):
        errors.append(f"the file must open `namespace {ns}` and close it with `end {ns}`")
    hs = hypotheses(code)
    k = len(hs)
    if not 2 <= k <= 4 or sorted(hs) != list(range(1, k + 1)):
        errors.append("declare 2 to 4 hypotheses `def H1 : Prop := …`, `def H2 : Prop := …` (numbered from 1, no gaps)")
    for i, txt in hs.items():
        if re.search(r"type_of%|\bmain\b|\bH[1-9]\b", txt) or (target.get("decl") and target["decl"] in txt) or target["statement"] in txt:
            errors.append(f"H{i} may not mention the target, another hypothesis or main")
        if len(txt) > 2000:
            errors.append(f"H{i} is longer than 2000 characters")
    if len(set(hs.values())) != len(hs):
        errors.append("two hypotheses are identical")
    others = re.findall(r"^\s*(?:noncomputable\s+)?(def|abbrev|structure|inductive|class|instance)\s+(\S+)", code, re.M)
    extra = [name for kind, name in others if not (kind == "def" and re.fullmatch(r"H[1-9]", name))]
    if extra:
        errors.append(f"only the H definitions may be declared (lemmas are fine): {', '.join(extra[:5])}")
    chain = r"\s*→\s*".join(f"H{i}" for i in range(1, k + 1))
    tgt = re.escape(target["statement"])
    if k and len(re.findall(r"\btheorem\s+main\s*:\s*" + chain + r"\s*→\s*" + tgt + r"\s*:=", code)) != 1:
        errors.append(f"must contain exactly one `theorem main : {' → '.join(f'H{i}' for i in range(1, k + 1))} → {target['statement']} := ...`")
    theorem = f"{ns}.main"
    out["hypotheses"] = [hs[i] for i in sorted(hs)]
    out["module"] = module_of(pid)

ok = not errors
out.update(ok=ok, kind=target["kind"], polarity=polarity, theorem=theorem, imports=target["import"], errors=errors)
if target.get("decl"):
    out["decl"] = target["decl"]
if target.get("reduction"):
    out["needsReduction"] = target["reduction"]
print(json.dumps(out, ensure_ascii=False))
sys.exit(0 if ok else 1)
