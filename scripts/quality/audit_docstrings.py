#!/usr/bin/env python3

import os
import re
import sys

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
        
    print(f"Auditing '{target_dir}' for missing declaration docstrings...\n")
    
    violations = run_audit(target_dir)
    
    if len(violations) > 0:
        print(f"Found {len(violations)} missing docstrings:\n")
        
        # Group by file
        grouped = {}
        for (f, l, msg) in violations:
            if f not in grouped:
                grouped[f] = []
            grouped[f].append((l, msg))
            
        for f in sorted(grouped.keys()):
            print(f"File: {f}")
            for l, msg in sorted(grouped[f]):
                print(f"  Line {l}: {msg}")
            print()
            
        print("Note: Mathlib strongly encourages/requires /-- docstrings for all definitions and major theorems.")
        sys.exit(1)
    else:
        print("No missing docstrings found! Great job!")
        sys.exit(0)
