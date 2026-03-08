#!/usr/bin/env python3

import os
import sys
import re

# Mathlib Style Guidelines:
# 1. Line length <= 100 characters.
# 2. Every file needs a module docstring `/-! ... -/`.
# 3. Prohibited characters / operators: `$` (use `<|` or `|>`), `λ` (use `fun` or `↦`).

def audit_file(filepath):
    violations = []
    
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        
    has_module_docstring = False
    
    for i, line in enumerate(lines):
        # 1. Check line length (using actual character count without newline)
        raw_line = line.rstrip('\n')
        if len(raw_line) > 100:
            # It's common to ignore long URLs in docstrings, but we will strictly flag lines over 100.
            # To reduce noise, we could ignore lines with URLs, but strict Mathlib style wraps them anyway.
            # We will ignore extreme long strings in JSON or generated files, but this targets .lean
            if 'http' not in raw_line and not raw_line.strip().startswith('--'):
                violations.append((filepath, i+1, f"Line exceeds 100 characters ({len(raw_line)})"))
                
        # 2. Check for module docstring block `/-!`
        if '/-!' in raw_line:
            has_module_docstring = True
            
        # 3. Check for prohibited operators: `$` and `λ`
        # `$` might be used in strings (e.g. s!"...) so we only flag if it's outside strings, but a simple 
        # regex checking for space before/after is decent approximation.
        if re.search(r'\s\$\s', raw_line):
           violations.append((filepath, i+1, "Usage of `$` operator is disallowed in Mathlib style. Use `<|` or `|>`."))
           
        if 'λ' in raw_line:
           violations.append((filepath, i+1, "Usage of `λ` is disallowed in Mathlib style. Use `fun` or `↦`."))

    # Report if module docstring is missing
    # (Some very short or specific files might be exceptions, but Mathlib strongly encourages them)
    if not has_module_docstring:
        violations.insert(0, (filepath, 0, "Missing module docstring `/-! ... -/` after imports."))

    return violations

def run_audit(directory_to_scan):
    all_violations = []
    
    for root, dirs, files in os.walk(directory_to_scan):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                violations = audit_file(filepath)
                all_violations.extend(violations)
                
    return all_violations

if __name__ == '__main__':
    target_dir = 'lean'
    if len(sys.argv) > 1:
        target_dir = sys.argv[1]
        
    print(f"Auditing '{target_dir}' for Mathlib style guidelines...\n")
    
    violations = run_audit(target_dir)
    
    if len(violations) > 0:
        print(f"Found {len(violations)} style rule violations:\n")
        
        # Group by file
        grouped = {}
        for (f, l, msg) in violations:
            if f not in grouped:
                grouped[f] = []
            grouped[f].append((l, msg))
            
        for f in sorted(grouped.keys()):
            print(f"File: {f}")
            for l, msg in sorted(grouped[f]):
                if l == 0:
                    print(f"  {msg}")
                else:
                    print(f"  Line {l}: {msg}")
            print()
            
        print("Note: To comply with Mathlib style, keep lines <= 100 chars, avoid `$` and `λ`, and include `/-!` module docstrings.")
        sys.exit(1)
    else:
        print("No style violations found! Great job!")
        sys.exit(0)
