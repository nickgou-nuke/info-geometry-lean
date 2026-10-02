#!/usr/bin/env python3
import sys
import re

target_file = ".agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean"
cheat_tokens = [
    "sorry", "admit", "native_decide", "unsafe", "axiom",
    "simpa using", "simp [", "TODO", "FIXME", "XXX",
    "dummy", "mock", "placeholder", "fake", "stub",
    "NotImplemented", "undefined", "panic!"
]

print(f"=== Scanning {target_file} for cheat tokens ===")
with open(target_file, "r", encoding="utf-8") as f:
    lines = f.readlines()

found_violations = []
for idx, line in enumerate(lines, 1):
    # Remove Lean comments: -- and /- ... -/
    # (Checking raw line as well as stripped line)
    clean_line = line.split("--")[0]
    for token in cheat_tokens:
        if token.lower() in clean_line.lower():
            # Check if it's within a docstring or comment
            found_violations.append((idx, token, line.strip()))

if found_violations:
    print(f"FAILED: Found {len(found_violations)} potential cheat tokens:")
    for lnum, tok, text in found_violations:
        print(f"  Line {lnum} [{tok}]: {text}")
else:
    print("PASSED: 0 cheat tokens found in clean code lines.")

print("\n=== Line-by-line inspection of all declarations ===")
in_structure = False
for idx, line in enumerate(lines, 1):
    sline = line.strip()
    if sline.startswith("def ") or sline.startswith("structure ") or sline.startswith("theorem ") or sline.startswith("lemma "):
        print(f"Line {idx:3d}: {sline}")
    elif sline == "rfl":
        print(f"Line {idx:3d}:   -> proof: rfl")
