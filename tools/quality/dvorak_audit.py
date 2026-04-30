#!/usr/bin/env python3
import json
import re
import argparse
from pathlib import Path

# Directive Mappings for Truth and Beauty
RULES = {
    "truth_believability": {
        "pattern": r"(theorem|lemma)\s+\w+\s*:=.*rfl",
        "message": "Potential Truth violation: Theorem closes by reflexivity (rfl). Check if definition is a 'mask' for an easy proof.",
        "dvorak_ref": "Thesis 1.3.1 (Truth)"
    },
    "vacuity_detected": {
        "pattern": r"sorry|sorryAx|Admission",
        "message": "Vacuity detected: Proof depends on trust tokens or is incomplete. Use Dvorak's Extend F or explicit algebraic structures to close edge cases.",
        "dvorak_ref": "Thesis 3.1.6 (Extended Fields)"
    },
    "believable_definition": {
        "pattern": r"noncomputable\s+def\s+\w+\s*:=.*classical\.choice",
        "message": "Nomological Rupture risk: Choice-based parameter admission without existence proof.",
        "dvorak_ref": "Thesis 2.6 (Axioms) & Directive X"
    }
}

def audit_file(path: Path):
    findings = []
    content = path.read_text()
    lines = content.splitlines()
    
    for i, line in enumerate(lines):
        for rule_name, rule in RULES.items():
            if re.search(rule["pattern"], line):
                findings.append({
                    "file": str(path),
                    "line": i + 1,
                    "rule": rule_name,
                    "message": rule["message"],
                    "reference": rule["dvorak_ref"]
                })
    return findings

def main():
    parser = argparse.ArgumentParser(description="Dvorak 'Truth and Beauty' Audit")
    parser.add_argument("--root", type=Path, default=Path("lean/InfoGeometry/Canonical"))
    parser.add_argument("--json-out", type=Path, default=Path("reports/dvorak-audit.json"))
    args = parser.parse_args()

    all_findings = []
    for lean_file in args.root.rglob("*.lean"):
        all_findings.extend(audit_file(lean_file))

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.json_out, "w") as f:
        json.dump(all_findings, f, indent=2)

    print(f"Audit complete. Found {len(all_findings)} issues.")
    print(f"Report written to {args.json_out}")

if __name__ == "__main__":
    main()
