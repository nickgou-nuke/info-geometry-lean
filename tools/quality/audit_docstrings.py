#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.quality.common import iter_lean_files, print_grouped_violations, resolve_target_dir
else:
    from tools.quality.common import iter_lean_files, print_grouped_violations, resolve_target_dir

# Mathlib Documentation Guidelines:
# Every definition, theorem, class, structure, etc., should ideally have a docstring
# introduced by `/--` and closed by `-/` right above it.

def audit_file(filepath):
    violations = []
    
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        
    in_docstring = False
    docstring_just_ended = False
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # Check if we are inside a docstring
        if stripped.startswith('/--'):
            in_docstring = True
            
        if in_docstring and '-/' in line:
            in_docstring = False
            docstring_just_ended = True
            continue
            
        # Ignore empty lines after docstring
        if docstring_just_ended and not stripped:
            continue
            
        # If we hit a declaration
        match = re.match(r'^(?:protected\s+|noncomputable\s+|private\s+|partial\s+)*(def|theorem|lemma|class|structure|inductive)\s+([a-zA-Z0-9_\']+)', line.lstrip())
        if match:
            decl_type = match.group(1)
            name = match.group(2)
            
            if not docstring_just_ended:
                violations.append((filepath, i+1, f"Missing docstring for {decl_type} '{name}'"))
            
            docstring_just_ended = False
        else:
            # If it's code but not a declaration, reset docstring state
            if stripped and not stripped.startswith('--') and not stripped.startswith('@[') and not stripped.startswith('attribute'):
                docstring_just_ended = False

    return violations

def run_audit(directory_to_scan):
    all_violations = []

    for path in iter_lean_files(directory_to_scan):
        violations = audit_file(str(path))
        all_violations.extend(violations)

    return all_violations

if __name__ == '__main__':
    target_dir = resolve_target_dir(sys.argv)
        
    print(f"Auditing '{target_dir}' for missing declaration docstrings...\n")
    
    violations = run_audit(target_dir)
    
    if len(violations) > 0:
        print(f"Found {len(violations)} missing docstrings:\n")
        
        print_grouped_violations(
            violations,
            item_formatter=lambda l, msg: f"  Line {l}: {msg}",
        )
            
        print("Note: Mathlib strongly encourages/requires /-- docstrings for all definitions and major theorems.")
        sys.exit(1)
    else:
        print("No missing docstrings found! Great job!")
        sys.exit(0)
