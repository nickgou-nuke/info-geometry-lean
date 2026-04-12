#!/usr/bin/env python3
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

"""
Semantic Audit Tool (The Sieve of Pauli)
Enforces signature stability and constitutional compliance for Lean 4 proofs.
Usage: python3 tools/infra/semantic_audit.py --task .tasks/my_task.json
"""


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def sha256_text(text: str) -> str:
    return hashlib.sha256(normalize_ws(text).encode("utf-8")).hexdigest()


def extract_decl_signature(content: str, decl_name: str) -> str | None:
    """Extract `(binders) : type` tail from theorem/lemma/def declaration."""
    pattern = rf"(?:theorem|lemma|def)\s+{re.escape(decl_name)}\b"
    match = re.search(pattern, content)
    if not match:
        return None

    i = match.end()
    n = len(content)
    depth_round = 0
    depth_square = 0
    depth_curly = 0
    sig_start = i

    while i < n:
        ch = content[i]
        nxt = content[i + 1] if i + 1 < n else ""

        if ch == "(":
            depth_round += 1
        elif ch == ")":
            depth_round = max(depth_round - 1, 0)
        elif ch == "[":
            depth_square += 1
        elif ch == "]":
            depth_square = max(depth_square - 1, 0)
        elif ch == "{":
            depth_curly += 1
        elif ch == "}":
            depth_curly = max(depth_curly - 1, 0)

        at_top_level = depth_round == 0 and depth_square == 0 and depth_curly == 0
        if at_top_level and ch == ":" and nxt == "=":
            return content[sig_start:i].strip()
        i += 1

    return None


def get_current_imports(content: str) -> list[str]:
    return re.findall(r"^\s*import\s+([\w\.]+)", content, re.MULTILINE)


def get_repo_root() -> Path:
    return Path(
        subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
    )


def get_git_file(ref: str, path_from_repo_root: str) -> str:
    return subprocess.check_output(
        ["git", "show", f"{ref}:{path_from_repo_root}"],
        text=True,
        stderr=subprocess.STDOUT,
    )


def import_delta_ok(
    current_content: str,
    baseline_content: str,
    allowed_imports: list[str],
) -> tuple[bool, list[str], list[str]]:
    current = set(get_current_imports(current_content))
    baseline = set(get_current_imports(baseline_content))
    added = sorted(current - baseline)
    unauthorized = [imp for imp in added if imp not in set(allowed_imports)]
    return (len(unauthorized) == 0, added, unauthorized)


def check_forbidden_constructs(content: str, constraints: list[str]) -> list[str]:
    lowered = {c.lower() for c in constraints}
    allow_classical = (
        "classical" in lowered
        or any("allow classical" in c for c in lowered)
        or any("authorized classical" in c for c in lowered)
    )
    allow_by_contra = (
        "by_contra" in lowered
        or any("allow by_contra" in c for c in lowered)
        or any("authorized by_contra" in c for c in lowered)
    )

    forbidden = ["sorry", "admit", "axiom"]
    if not allow_classical:
        forbidden.extend(["Classical.choice", "classical"])
    if not allow_by_contra:
        forbidden.append("by_contra")

    findings: list[str] = []
    for token in forbidden:
        if re.search(rf"\b{re.escape(token)}\b", content):
            findings.append(token)
    return findings


def validate_task_schema(task: dict) -> None:
    required = [
        "taskId",
        "targetFile",
        "theoremName",
        "expectedType",
        "budget",
        "constraints",
    ]
    missing = [k for k in required if k not in task]
    if missing:
        raise ValueError(f"Task manifest is missing required keys: {', '.join(missing)}")
    if "imports" not in task["budget"]:
        raise ValueError("Task manifest budget must include `imports`.")
    if not isinstance(task["budget"]["imports"], list):
        raise ValueError("Task manifest budget.imports must be a list.")
    if "statementHash" in task and not isinstance(task["statementHash"], str):
        raise ValueError("Task manifest statementHash must be a string when provided.")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--task", required=True, help="Path to task manifest JSON.")
    args = parser.parse_args()

    task_path = Path(args.task)
    if not task_path.exists():
        print(f"FAILED: manifest not found: {task_path}")
        sys.exit(1)

    with task_path.open("r", encoding="utf-8") as f:
        task = json.load(f)

    try:
        validate_task_schema(task)
    except ValueError as exc:
        print(f"FAILED: {exc}")
        sys.exit(1)

    target_file = Path(task["targetFile"])
    if not target_file.exists():
        print(f"FAILED: target file not found: {target_file}")
        sys.exit(1)

    content = target_file.read_text(encoding="utf-8")

    print(f"--- [AUDIT] Processing {task['theoremName']} ---")

    current_signature = extract_decl_signature(content, task["theoremName"])
    if not current_signature:
        print(f"FAILED: declaration {task['theoremName']} not found in source")
        sys.exit(1)

    expected = normalize_ws(task["expectedType"])
    actual = normalize_ws(current_signature)
    if expected != actual:
        print("FAILED: semantic drift detected in declaration signature")
        print(f"Expected: {expected}")
        print(f"Actual:   {actual}")
        sys.exit(1)
    print("SUCCESS: Signature identity verified.")

    statement_hash = task.get("statementHash")
    if statement_hash:
        actual_hash = sha256_text(actual)
        if actual_hash != statement_hash:
            print("FAILED: statement hash mismatch")
            print(f"Expected hash: {statement_hash}")
            print(f"Actual hash:   {actual_hash}")
            sys.exit(1)
        print("SUCCESS: Statement hash verified.")

    repo_root = get_repo_root()
    if target_file.is_absolute():
        target_rel = target_file.relative_to(repo_root).as_posix()
    else:
        target_rel = target_file.as_posix()

    baseline_ref = task.get("baselineRef", "HEAD~1")
    try:
        baseline_content = get_git_file(baseline_ref, target_rel)
    except subprocess.CalledProcessError as exc:
        print(f"FAILED: could not load baseline {baseline_ref}:{target_rel}")
        print(exc.output.strip())
        sys.exit(1)

    ok, added, unauthorized = import_delta_ok(
        content,
        baseline_content,
        task["budget"].get("imports", []),
    )
    if not ok:
        print("FAILED: unauthorized import creep detected")
        print(f"Added imports:        {added}")
        print(f"Unauthorized imports: {unauthorized}")
        sys.exit(1)
    print("SUCCESS: Import delta verified.")

    violations = check_forbidden_constructs(content, task.get("constraints", []))
    if violations:
        print(f"FAILED: forbidden constructs detected: {', '.join(sorted(set(violations)))}")
        sys.exit(1)
    print("SUCCESS: Pauli sieve passed.")

    print(f"--- [RESULT] AUDIT PASSED for {task['taskId']} ---")


if __name__ == "__main__":
    main()
