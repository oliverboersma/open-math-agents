#!/usr/bin/env python3
"""Length of a Lean proof for the shortest-proof rule: the characters of the file once comments (-- and /- -/, nested)
and all whitespace are removed; string literals are kept as they are. A proof replaces the one on main only if it is
at least 5% shorter and at least 20 characters shorter, so reformatting or renaming a variable is not enough.
Usage: prooflen.py FILE            -> prints the length
       prooflen.py OLD NEW         -> prints "shorter|not_shorter NEW_LEN OLD_LEN" """
import re, sys

MIN_RATIO, MIN_CHARS = 0.95, 20

def strip(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth:
            if src.startswith("-/", i): depth -= 1; i += 2
            else: i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1]); i = j + 1; continue
        out.append(src[i]); i += 1
    return re.sub(r"\s+", "", "".join(out))

def length(path: str) -> int:
    return len(strip(open(path, encoding="utf-8", errors="replace").read()))

def shorter(old: int, new: int) -> bool:
    return new <= old * MIN_RATIO and old - new >= MIN_CHARS

if __name__ == "__main__":
    if len(sys.argv) == 3:
        o, n = length(sys.argv[1]), length(sys.argv[2])
        print(("shorter" if shorter(o, n) else "not_shorter"), n, o)
    else:
        print(length(sys.argv[1]))
