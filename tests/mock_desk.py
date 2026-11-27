#!/usr/bin/env python3
"""A stand-in for the site, for testing tools/oma.sh. Logs every request to $MOCK_LOG (one JSON per line)."""
import json, os, sys, urllib.parse
from http.server import BaseHTTPRequestHandler, HTTPServer

LOG = os.environ["MOCK_LOG"]
PID = "Erdos3.erdos_3.variants.gowers"

class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, body, ctype="application/json"):
        b = (json.dumps(body) if not isinstance(body, str) else body).encode()
        self.send_response(code); self.send_header("Content-Type", ctype); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
    def handle_any(self):
        u = urllib.parse.urlparse(self.path); q = dict(urllib.parse.parse_qsl(u.query))
        open(LOG, "a").write(json.dumps({"method": self.command, "path": u.path, "q": q}) + "\n")
        if u.path == "/api/desk/next":
            pid = q.get("problem") or PID
            if q.get("kind") == "formalize":
                return self.send(200, {"lease": "11111111-1111-1111-1111-111111111111", "task": "formalize", "points": 0,
                    "problem": {"id": "opg-x", "title": "X", "kind": "unformalized", "source": "OPG", "ref": "https://x"},
                    "file": "statements/opg-x.lean", "skeleton": "import Mathlib\n-- statement skeleton\n", "othersWorking": 0, "instructions": "state it"})
            if pid == "nope":
                return self.send(404, {"error": "not_found", "hint": "no such problem"})
            return self.send(200, {"lease": "22222222-2222-2222-2222-222222222222", "points": 39,
                "problem": {"id": pid, "title": "Erdős 3 gowers", "kind": "known", "difficulty": 53, "source": "Erdős Problems",
                            "statement": "For every k...", "lean": "theorem t : True", "page": "http://x/p/" + pid},
                "othersWorking": 1, "role": "checker", "roleTask": "Test the statement.", "team": [{"handle": "mate", "role": "lead"}],
                "teamNotes": [], "lastNote": 7, "collaboration": "TEAMWORK PROTOCOL", "file": f"proofs/{pid}.lean", "skeleton": f"import FormalConjectures.ErdosProblems.«3»\n\ntheorem OMA.solution : type_of% @{pid} := by\n  sorry\n"})
        if u.path == "/api/desk/beat":
            if q.get("lease", "").startswith("3333"):
                return self.send(410, {"stop": True, "status": "settled"})
            since = int(q.get("since", "0") or 0)
            notes = [{"id": 41, "handle": "mate", "at": "2026-11-27T09:00:00Z", "note": "PLAN: induction on k, need lemma L1"}]
            return self.send(200, {"ok": True, "role": "checker", "roleTask": "Test the statement.",
                                   "team": [{"handle": "mate", "role": "lead"}],
                                   "notes": [n for n in notes if n["id"] > since], "last_note": 41})
        if u.path == "/api/desk/release":
            return self.send(200, {"ok": True})
        if u.path.startswith("/p/") and u.path.endswith("/agent.txt"):
            return self.send(200, "BRIEF FOR " + urllib.parse.unquote(u.path[3:-10]) + "\n", "text/plain")
        if u.path.startswith("/api/problems/"):
            n = q.get("reduction", "1")
            return self.send(200, {"reductionSkeleton": f"import X\nnamespace OMA.R_{n}\ndef H1 : Prop := sorry\nend OMA.R_{n}\n"})
        if u.path == "/api/stats":
            return self.send(200, {"liveAgents": 3, "solved": []})
        return self.send(404, {"error": "mock: unknown path"})
    do_GET = handle_any
    do_POST = handle_any

HTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
