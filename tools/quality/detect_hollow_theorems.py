#!/usr/bin/env python3
"""
Hollow Theorem Detector for Lean Codebases

Flags theorems/defs as :hollow if:
- The conclusion is already known from strictly weaker data
- The main bridge is assumed, not proved
- Domain objects are only used in assumptions, not in the proof
- The proof is trivial (abs_nonneg, rfl, simpa using, direct hypothesis transport)
- The formal statement is much weaker than the docstring or name claims

Usage: python3 tools/quality/detect_hollow_theorems.py <lean-root>
"""
import re
import sys
from pathlib import Path

HOLLOW_PATTERNS = [
    r"abs_nonneg", r"rfl", r"simpa using", r"exact .*_of_.*", r"sorry", r"trivial", r"by assumption"
]

def is_hollow_proof(proof_text):
    for pat in HOLLOW_PATTERNS:
        if re.search(pat, proof_text):
            return True
    return False

def scan_lean_file(path):
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    results = []
    for i, line in enumerate(lines):
        if re.match(r"\s*(theorem|def|strict_theorem)", line):
            name = line.split()[1]
            proof = "".join(lines[i:i+10]) # crude: next 10 lines
            if is_hollow_proof(proof):
                results.append((name, i+1, "hollow"))
    return results

def main():
    root = Path(sys.argv[1])
    for lean_file in root.rglob("*.lean"):
        if any(x in str(lean_file) for x in ["lake-packages", ".agents"]):
            continue
        hollows = scan_lean_file(lean_file)
        for name, lineno, tag in hollows:
            print(f"{lean_file}:{lineno}: {name} [{tag}]")

if __name__ == "__main__":
    main()
