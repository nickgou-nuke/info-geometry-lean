#!/usr/bin/env python3
import json
import re
import sys
import subprocess
from pathlib import Path

"""
# Semantic Audit Tool (The Sieve of Pauli)
Enforces signature stability and constitutional compliance for Lean 4 proofs.
Usage: python3 semantic_audit.py --task .tasks/my_task.json
"""

def extract_theorem_signature(content, theorem_name):
    # Matches: theorem name ... : type :=
    # Multiline support
    pattern = rf"(?:theorem|lemma|def)\s+{re.escape(theorem_name)}[\s\S]*?:\s*([\s\S]*?)(?::=|\n\n|\Z)"
    match = re.search(pattern, content)
    if match:
        return match.group(1).strip()
    return None

def check_forbidden_tactics(content, allowed=[]):
    forbidden = ["sorry", "axiom"]
    if "classical" not in allowed:
        forbidden.append("Classical.choice")
        forbidden.append("classical")
    if "by_contra" not in allowed:
        forbidden.append("by_contra")
    
    findings = []
    for f in forbidden:
        if re.search(rf"\b{re.escape(f)}\b", content):
            findings.append(f)
    return findings

def get_current_imports(content):
    return re.findall(r"^import\s+([\w\.]+)", content, re.MULTILINE)

def main():
    if len(sys.argv) < 3 or sys.argv[1] != "--task":
        print("Usage: python3 semantic_audit.py --task <path_to_task.json>")
        sys.exit(1)

    task_path = Path(sys.argv[2])
    if not task_path.exists():
        print(f"Error: Task manifest {task_path} not found.")
        sys.exit(1)

    with open(task_path, "r") as f:
        task = json.load(f)

    target_file = Path(task["targetFile"])
    if not target_file.exists():
        print(f"Error: Target file {target_file} not found.")
        sys.exit(1)

    with open(target_file, "r") as f:
        content = f.read()

    print(f"--- [AUDIT] Processing {task['theoremName']} ---")

    # 1. Signature Lock Check
    current_signature = extract_theorem_signature(content, task["theoremName"])
    if not current_signature:
        print(f"FAILED: Theorem {task['theoremName']} not found in source.")
        sys.exit(1)

    # Normalize whitespace for comparison
    expected = re.sub(r"\s+", " ", task["expectedType"]).strip()
    actual = re.sub(r"\s+", " ", current_signature).strip()

    if expected != actual:
        print("FAILED: Semantic Drift detected in Theorem Signature!")
        print(f"Expected: {expected}")
        print(f"Actual:   {actual}")
        sys.exit(1)
    print("SUCCESS: Signature Identity Verified.")

    # 2. Import Pollution Check
    current_imports = get_current_imports(content)
    allowed_imports = task["budget"].get("imports", [])
    
    # This check is tricky because the file might already have imports.
    # We should track the 'delta'. 
    # For now, we alert if any NEW imports are added that aren't in the budget.
    # (Implementation detail: this script assumes it's comparing against a baseline)
    pass # TODO: Implement import diffing against baseline

    # 3. Forbidden Tactics (Sieve of Pauli)
    violations = check_forbidden_tactics(content, task.get("constraints", []))
    if violations:
        print(f"FAILED: Forbidden constructs detected: {', '.join(violations)}")
        sys.exit(1)
    print("SUCCESS: Pauli Sieve passed (no sorry/axiom/unauthorized classical).")

    print(f"--- [RESULT] AUDIT PASSED for {task['taskId']} ---")

if __name__ == "__main__":
    main()
