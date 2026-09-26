#!/usr/bin/env python3
import os
import re
import sys

live_path = "lean/InfoGeometry/LLM/KreinAttentionEnergy.lean"
sandbox_path = ".agents/sandbox_krein/lean/InfoGeometry/LLM/KreinAttentionEnergy.lean"

# 1. Token scan
forbidden_tokens = ["sorry", "admit", "native_decide", "unsafe", "axiom ", "simpa using", "simp ["]
with open(sandbox_path, "r") as f:
    sandbox_content = f.read()

violations = []
for line_num, line in enumerate(sandbox_content.splitlines(), 1):
    clean_line = line.split("--")[0]  # ignore comments
    for token in forbidden_tokens:
        if token in clean_line:
            violations.append((line_num, token, line))

with open(".agents/sandbox_krein/audit/audit_token_scan.log", "w") as f:
    f.write("Token Scan Audit Report\n")
    f.write(f"Target: {sandbox_path}\n")
    f.write(f"Forbidden tokens checked: {forbidden_tokens}\n")
    if violations:
        f.write(f"Violations found: {len(violations)}\n")
        for line_num, tok, line in violations:
            f.write(f"  Line {line_num}: token '{tok}' in: {line.strip()}\n")
    else:
        f.write("Violations found: 0 (PASSED: 0 sorry, 0 admit, 0 native_decide, 0 simpa using, 0 simp storms)\n")

# 2. Declaration Fidelity
def extract_decls(filepath):
    decls = []
    decl_regex = re.compile(r"^(?:noncomputable\s+)?(structure|def|theorem|inductive|abbrev|axiom|lemma)\s+([A-Za-z0-9_]+)", re.MULTILINE)
    with open(filepath, "r") as f:
        content = f.read()
    for match in decl_regex.finditer(content):
        decls.append((match.group(1), match.group(2)))
    return decls

live_decls = extract_decls(live_path)
sandbox_decls = extract_decls(sandbox_path)

live_names = [name for kind, name in live_decls]
sandbox_names = [name for kind, name in sandbox_decls]

missing = [d for d in live_names if d not in sandbox_names]
extra = [d for d in sandbox_names if d not in live_names]

with open(".agents/sandbox_krein/audit/audit_declaration_fidelity.log", "w") as f:
    f.write("Declaration Fidelity Audit Report\n")
    f.write(f"Live file: {live_path} (total {len(live_decls)})\n")
    f.write(f"Sandbox file: {sandbox_path} (total {len(sandbox_decls)})\n")
    f.write(f"Missing live declarations count: {len(missing)}\n")
    f.write(f"Fidelity rate: {100.0 * (len(live_decls) - len(missing)) / len(live_decls):.1f}%\n\n")
    f.write("Live Declarations Status:\n")
    for kind, name in live_decls:
        status = "OK" if name in sandbox_names else "MISSING"
        f.write(f"  [{status}] {kind} {name}\n")
    if extra:
        f.write("\nNew Declarations Added:\n")
        for name in extra:
            f.write(f"  [ADDED] {name}\n")

print("Audits executed successfully.")
