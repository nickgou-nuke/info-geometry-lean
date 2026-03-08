#!/usr/bin/env python3

import os
import re
import sys
from pathlib import Path

# Mathlib Naming Conventions:
# 1. Terms of Props (proofs, theorem, lemma) use snake_case.
# 2. Props and Types (or Sort) (inductive types, structures, classes) use UpperCamelCase.
# 3. All other terms of Types (defs) use lowerCamelCase (unless they return a Type/Prop).

def is_snake_case(s):
    # Allows trailing numbers or primes, e.g., foo_bar, foo_bar', foo1 
    return re.match(r'^[a-z0-9_]+[\']*$', s) is not None

def is_upper_camel_case(s):
    # Allows UpperCamelCase, numbers, and primes.
    return re.match(r'^[A-Z][a-zA-Z0-9_]*[\']*$', s) is not None

def is_lower_camel_case(s):
    # Allows lowerCamelCase, numbers, and primes.
    return re.match(r'^[a-z][a-zA-Z0-9_]*[\']*$', s) is not None

def audit_file(filepath):
    violations = []
    
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        
    for i, line in enumerate(lines):
        # Clean up line to avoid comments
        code = line.split('--')[0].strip()
        
        # 1. Theorems and Lemmas should be snake_case
        theorem_match = re.match(r'^(theorem|lemma)\s+([a-zA-Z0-9_\']+)', code)
        if theorem_match:
            name = theorem_match.group(2)
            if not is_snake_case(name):
                # Ignore things that are explicitly namespaced with UpperCamelCase prefixes for now
                if '.' in name:
                    parts = name.split('.')
                    if not is_snake_case(parts[-1]):
                         violations.append((filepath, i+1, f"Theorem/lemma '{name}' should be snake_case"))
                else:
                    violations.append((filepath, i+1, f"Theorem/lemma '{name}' should be snake_case"))
                    
        # 2. Defs (that don't obviously return Prop/Type) should be lowerCamelCase
        # This regex is simplified, it just finds the name. 
        # Lean 4 return types can be complex, but if a def starts with an uppercase letter, it's a flag.
        def_match = re.match(r'^def\s+([a-zA-Z0-9_\']+)', code)
        if def_match:
            name = def_match.group(1)
            # Skip namespaced defs for this simple check
            if '.' not in name:
                # If it's UpperCamelCase, it MIGHT be valid if it returns a Type/Prop.
                # We'll flag it for review if it's strictly UpperCamelCase
                if is_upper_camel_case(name):
                    # Check if 'Prop' or 'Type' is in the signature on the same line
                    if 'Prop' not in code and 'Type' not in code and 'Sort' not in code:
                        violations.append((filepath, i+1, f"Definition '{name}' returns a value (not Prop/Type) but is UpperCamelCase. Should be lowerCamelCase."))

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
        
    print(f"Auditing '{target_dir}' for Mathlib naming conventions...\n")
    
    violations = run_audit(target_dir)
    
    if len(violations) > 0:
        print(f"Found {len(violations)} potential naming convention violations:\n")
        
        # Group by file
        grouped = {}
        for (f, l, msg) in violations:
            if f not in grouped:
                grouped[f] = []
            grouped[f].append((l, msg))
            
        for f in sorted(grouped.keys()):
            print(f"File: {f}")
            for (l, msg) in sorted(grouped[f]):
                print(f"  Line {l}: {msg}")
            print()
            
        print("Note: Some defs returning Types/Props might be flagged if the return type is on a newline or inferred.")
        print("Please review the flagged names against https://leanprover-community.github.io/contribute/naming.html")
        sys.exit(1)
    else:
        print("No naming convention violations found! Great job!")
        sys.exit(0)
