#!/usr/bin/env python3
"""
Closure AST Validator: Ensures only allowed Lean AST node types are present in closure modules.
Requires: ast_export (Lean 4), Python 3.8+
"""
import argparse
import json
import sys
from pathlib import Path

ALLOWED_KINDS = {"theorem", "lemma", "def", "structure", "inductive", "class"}
BANNED_KINDS = {"axiom", "postulate"}


def validate_ast(ast_path: Path) -> int:
    with ast_path.open(encoding="utf-8") as f:
        ast = json.load(f)
    errors = []
    for decl in ast.get("declarations", []):
        kind = decl.get("kind", "")
        name = decl.get("name", "")
        if kind in BANNED_KINDS:
            errors.append(f"BANNED kind: {kind} in {name}")
        elif kind not in ALLOWED_KINDS:
            errors.append(f"Disallowed kind: {kind} in {name}")
        if decl.get("hasSorry", False):
            errors.append(f"SORRY in {name}")
        if decl.get("hasAdmit", False):
            errors.append(f"ADMIT in {name}")
    if errors:
        print("[FAIL] AST validation errors:")
        for e in errors:
            print("-", e)
        return 1
    print("[PASS] AST validation: all declarations allowed.")
    return 0


def main():
    p = argparse.ArgumentParser(description="Validate Lean AST for closure discipline.")
    p.add_argument("--ast", required=True, help="Path to Lean AST JSON file (from ast_export).")
    args = p.parse_args()
    sys.exit(validate_ast(Path(args.ast)))

if __name__ == "__main__":
    main()
