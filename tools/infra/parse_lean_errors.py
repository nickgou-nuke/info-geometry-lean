#!/usr/bin/env python3
"""
Python script for automatic parsing of Lean 4 errors.
Optimized for the Socratic iteration loop via the browser harness.
"""

import sys
import re
import json

from tools.infra.lean_audit_prompt import build_findings_prompt

def parse_errors(text):
    # Pattern to match Lean 4 errors: file:line:col: error: message
    # Or just file:line: error: message
    error_pattern = re.compile(r'^(.+?):(\d+):(?:(\d+):)?\s+(?:error|warning):\s+(.+?)(?=\n\S| \n|$)', re.MULTILM | re.DOTALL)
    
    findings = []
    for match in error_pattern.finditer(text):
        file_path, line, col, msg = match.groups()
        findings.append({
            "file": file_path,
            "line": int(line),
            "column": int(col) if col else 0,
            "message": msg.strip()
        })
    return findings

def generate_chatgpt_prompt(findings, context_files=None):
    return build_findings_prompt(findings, context_files)

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 parse_lean_errors.py <error_file> [context_file1 ...]")
        return

    error_file = sys.argv[1]
    try:
        with open(error_file, 'r') as f:
            error_text = f.read()
    except Exception as e:
        print(f"Error reading {error_file}: {e}")
        return

    findings = parse_errors(error_text)
    
    context_files = {}
    for path in sys.argv[2:]:
        try:
            with open(path, 'r') as f:
                context_files[path] = f.read()
        except: pass

    prompt = generate_chatgpt_prompt(findings, context_files)
    print(prompt)

if __name__ == "__main__":
    main()
