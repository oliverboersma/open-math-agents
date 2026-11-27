#!/usr/bin/env python3
"""Add open conjectures stated in arXiv math abstracts to data/extra2.json.

Input: JSON lines from the arXiv API (id, title, summary, published, authors, primary category), harvested with
queries such as abs:"we conjecture" or abs:"remains open" per math category. arXiv metadata, abstracts included,
is CC0. Kept: abstracts that POSE a conjecture or an open question ("we conjecture", "conjecture that ...",
"remains open", "open problem/question", "we pose"). Dropped: abstracts where the paper settles it ("we prove the
conjecture", "confirming", "disproving", "answering an open question", "counterexample to"), unless it also poses a
new one; history/general-math categories; papers already in the catalogue (formal-conjectures arXiv entries).
One entry per paper; the statement leads with the sentences that state the conjecture, then the abstract.
Also dropped: "remains open" stated as the motivation of a paper that then proves/answers it; sentences that only
announce open questions without stating them ("we state some open questions"); non-math primary categories (vague
"remains an open problem" sentences in applied papers); papers before MIN_YEAR (older conjectures are more likely to
have been settled since). Every entry says it is open as stated in the paper and was not re-checked against later work.

Usage: python3 -I scripts/ingest_arxiv_conjectures.py <raw.jsonl>
"""
import json, os, re, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRA2 = os.path.join(HERE, "..", "data", "extra2.json")
CATALOG = os.path.join(HERE, "..", "data", "catalog.json")
SRC = "arXiv abstracts (not formalized)"
LICENSE = "Abstract from arXiv (metadata CC0); the conjecture is the authors', see the paper"

FIELD = {"NT": "Number Theory", "CO": "Combinatorics", "AG": "Algebraic Geometry", "GT": "General Topology", "GR": "Group Theory",
         "PR": "Probability", "AP": "PDEs", "CA": "Real Functions", "DS": "Dynamical Systems", "FA": "Functional Analysis",
         "OA": "Operator Theory", "RT": "Group Theory", "LO": "Logic & Foundations", "MG": "Convex & Discrete Geometry",
         "DG": "Manifolds", "AT": "General Topology", "CV": "Complex Analysis", "RA": "Associative Rings", "AC": "Commutative Algebra",
         "SP": "Operator Theory", "CT": "Category Theory", "KT": "K-Theory", "GN": "General Topology", "QA": "Quantum Theory",
         "SG": "Manifolds", "IT": "Information & Communication", "OC": "Approximation", "ST": "Probability", "NA": "Approximation",
         "MP": "Quantum Theory"}
SKIP_CATS = {"HO", "GM"}

# Only the reliable phrasings: the authors themselves say it is open, or conjecture it.
POSE = re.compile(r"(?i)\b(we (also |further |now )?conjecture|it is natural to conjecture|we (pose|formulate|propose|state) (a |an |the |several |two |some )?(conjecture|question|problem|open)|we ask whether|we raise (the |an |a )?(question|problem)|remains? (an )?open|remain open|(is|are) still open|left open|we leave [^.]{0,60} open|conjecture that|(it is|is|was|remains|has remained|it has remained|remained) (still |currently |largely |at present |a |an ){0,3}(long-?standing |well-known |famous |major |important |natural |interesting |challenging |notoriously )?open (problem|question)|(it is|is) (still |currently )?(open|unknown|not known) (whether|if|how)|an open (problem|question) (is|asks)|the (open )?question (of whether|whether) [^.]{0,120} (is|remains) (open|unanswered|unknown)|we ask (whether|if))")
# A sentence that answers, proves or settles something is not an open statement (even "partially").
SETTLE = re.compile(r"(?i)\b(prove[sd]?|proof of|proving|confirm(s|ed|ing)?|establish(es|ed|ing)?|resolve[sd]?|resolving|settle[sd]?|settling|disprove[sd]?|disproving|refute[sd]?|refuting|answer(s|ed|ing)?|verify|verifies|verified|solve[sd]?|solving|solution (to|of)|counterexample)\b[^.]{0,90}\b(conjecture|question|problem)\b")
OTHERS = re.compile(r"(?i)\b(posed by|raised by|asked by|proposed by|due to|question of [A-Z]|problem of [A-Z]|conjecture of [A-Z])\b")
NEW = re.compile(r"(?i)\b(we (also |further |now )?conjecture|we pose|we formulate|remains? open|remain open|(is|are) still open|left open|we ask|(open|unknown|not known) whether|open (problem|question))\b")
MIN_YEAR = 2018
# Statements that are new (the authors' own conjecture/question), as opposed to "X remains open" setting up the paper.
OWN = re.compile(r"(?i)\b(we (also |further |now )?conjecture|it is natural to conjecture|we (pose|formulate|propose|state) (a |an |the |two |several )?(conjecture|question|problem|open problem)|we ask whether|we raise)\b")
# The paper itself then proves/answers something.
LATER_WIN = re.compile(r"(?i)\b(in this (paper|note|article|work)|here|we)\b[^.]{0,40}\b(prove|show|establish|resolve|answer|settle|solve|confirm|disprove|refute|give an affirmative|give a negative|determine)\b")
# Sentences that only announce open questions, with no content.
EMPTY = re.compile(r"(?i)\b(some|several|a few|a number of|various|related|further|many|other|list of|state|discuss|mention|present|conclude with|close with|end with|we pose|we raise)\b[^.]{0,30}\bopen (questions|problems)\b(?![^.]{0,10}(:|whether|of whether|concerning the|on the existence))|\bopen (questions|problems) (are|is) (also )?(discussed|mentioned|listed|presented|posed|raised|stated|given|formulated)\b|\bwith (some|several|a few)? ?(open )?(questions|problems)\.?$|\b(pose|raise|state|list|discuss|propose|formulate|mention) (some|several|a few|a number of|various|many|further|related|two|three|new) (\w+ )?(questions|problems|conjectures)\b(?![^.]{0,12}(:|whether))|\b(many|several|some|various|numerous|a number of|other) (\w+ )?(questions|problems) (remain|are still|still remain) (open|unanswered|unsolved)|\bpropose (a|some|several) conjectures?( (concerning|about|on|regarding)[^.$]{0,80})?\.?$|\b(state|propose|formulate|pose|make|present|give) (a|an|one|the following|some) (new )?(conjecture|question|problem)s?\b(?![^.]{0,25}\b(that|whether|on|concerning|about|regarding|for|in|of|which|stating|asserting)\b)(?![^.]{0,25}:)")
VAGUE = re.compile(r"(?i)\b(data|neural|learning|automated|in practice|challenge|practitioners|engineering|real-world|machine)\b")
SENT = re.compile(r"(?<=[.!?])\s+(?=[A-Z$\\(])")

def norm(s):
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()

raw = {}
for line in open(sys.argv[1], encoding="utf-8"):
    r = json.loads(line); raw[r["id"]] = r

cat = json.load(open(CATALOG, encoding="utf-8"))["problems"]
in_core = set()
for p in cat:
    for m in re.finditer(r"(\d{4}\.\d{4,5})", p["id"] + " " + (p.get("ref") or "")):
        in_core.add(m.group(1))
d = json.load(open(EXTRA2, encoding="utf-8"))
have = {r[0] for r in d["rows"]}
titles = {norm(r[1]) for r in d["rows"]} | {norm(p["title"]) for p in cat}
if SRC not in d["sources"]: d["sources"].append(SRC)
d["licenses"][SRC] = LICENSE
si = d["sources"].index(SRC)

drop = collections.Counter(); added = []
for aid, r in raw.items():
    pc = (r.get("primary") or "").split(".")
    sub = pc[1] if len(pc) > 1 and pc[0] == "math" else None
    if sub is None:  # cross-listed into math: use the first math category
        sub = next((c.split(".")[1] for c in r.get("cats", []) if c.startswith("math.") and "." in c), None)
    if sub is None or sub in SKIP_CATS: drop["category"] += 1; continue
    if not (r.get("primary") or "").startswith("math"): drop["non_math_primary"] += 1; continue
    year = int(r["published"][:4]) if r.get("published") else 2000
    if year < MIN_YEAR: drop["before_" + str(MIN_YEAR)] += 1; continue
    s = r["summary"]
    sents = [x.strip() for x in SENT.split(s) if x.strip()]
    posing = [x for x in sents if POSE.search(x) and not SETTLE.search(x) and not (OTHERS.search(x) and not NEW.search(x))
              and not re.search(r"(?i)\bopen (and|dense|set|subset|map|cover|ball|neighbou?rhood|disc|disk)\b|\bopen in\b", x)
              and not re.search(r"(?i)conjecture that[^.]{0,120}\b(was|has been|had been|is now) (proved|proven|disproved|shown|established)", x)]
    if not posing: drop["no_open_statement"] += 1; continue
    # drop content-free announcements and vague applied sentences
    posing = [x for x in posing if not EMPTY.search(x) and not (VAGUE.search(x) and "$" not in x) and len(x) >= 50]
    if not posing: drop["no_stated_content"] += 1; continue
    # "X remains open. In this paper we prove X" : the open statement is the paper's motivation, not an open problem.
    first = sents.index(posing[0])
    if not OWN.search(" ".join(posing)) and any(LATER_WIN.search(x) for x in sents[first + 1:]):
        drop["answered_in_paper"] += 1; continue
    if SETTLE.search(s) and not any(NEW.search(x) for x in posing): drop["settled_in_paper"] += 1; continue
    base = aid.replace("/", "_")
    rid = f"arxiv-{base}"
    if rid in have or aid in in_core: drop["already_listed"] += 1; continue
    if norm(r["title"]) in titles: drop["same_title"] += 1; continue
    head = " ".join(posing[:2])
    statement = head if len(s) <= len(head) + 20 else (head + "\n\n" + s)
    if len(statement) > 1400: statement = statement[:1350].rsplit(" ", 1)[0] + " …"
    fame = 18 + max(0, min(14, year - 2012))  # newer = more likely still open
    added.append([rid, r["title"][:200], si, [FIELD.get(sub, "Number Theory")], statement, f"https://arxiv.org/abs/{aid}",
                  r.get("authors", [])[:6], fame, 70, [f"math.{sub}", r["published"][:4]], f"Open as stated in arXiv {aid} ({r['published'][:10]}); not re-checked against later work", 0])
    have.add(rid); titles.add(norm(r["title"]))

d["rows"].extend(added)
d["meta"]["counts"][SRC] = sum(1 for x in d["rows"] if x[2] == si)
d["meta"]["total"] = len(d["rows"])
d["meta"]["arxiv"] = {"harvested": len(raw), "added": len(added), "dropped": dict(drop)}
json.dump(d, open(EXTRA2, "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
print(json.dumps({"harvested": len(raw), "added": len(added), "dropped": dict(drop), "total_rows": len(d["rows"])}))
