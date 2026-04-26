#!/usr/bin/env python3
"""
Ornamental Hypothesis Detector for Lean Codebases

Flags theorems/defs as :ornamental if:
- The main domain object appears only in the assumptions, not in the proof body
- There are dead let bindings for domain lemmas that are never used
- The proof is just a transport of a previously known result

Usage: python3 tools/quality/detect_ornamental_hypotheses.py <lean-root>
"""
import re
import sys
from pathlib import Path

def scan_lean_file(path):
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    results = []
    for i, line in enumerate(lines):
        if re.match(r"\s*(theorem|def|strict_theorem)", line):
            name = line.split()[1]
            # Look for dead let bindings
            for j in range(i, min(i+10, len(lines))):
                if re.match(r"\s*let _[a-zA-Z0-9_]*\s*:", lines[j]):
                    results.append((name, j+1, "ornamental-dead-let"))
            # Look for domain objects only in assumptions
            if re.search(r"\(.*Connes.*\)", line) and not any("Connes" in l for l in lines[i+1:i+10]):
                results.append((name, i+1, "ornamental-domain-object"))
    return results

def main():
    root = Path(sys.argv[1])
    for lean_file in root.rglob("*.lean"):
        if any(x in str(lean_file) for x in ["lake-packages", ".agents"]):
            continue
        ornaments = scan_lean_file(lean_file)
        for name, lineno, tag in ornaments:
            print(f"{lean_file}:{lineno}: {name} [{tag}]")

if __name__ == "__main__":
    main()
