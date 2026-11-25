#!/usr/bin/env python3
"""Check a fresh Lean axiom log against an explicit audit source inventory."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})


def without_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments from audit source."""
    result: list[str] = []
    depth = 0
    index = 0
    while index < len(source):
        if source.startswith('/-', index):
            depth += 1
            result.append(' ')
            index += 2
        elif depth and source.startswith('-/', index):
            depth -= 1
            result.append(' ')
            index += 2
        elif depth:
            if source[index] == '\n':
                result.append('\n')
            index += 1
        elif source.startswith('--', index):
            end = source.find('\n', index)
            index = len(source) if end < 0 else end
        else:
            result.append(source[index])
            index += 1
    if depth:
        raise ValueError('Unterminated block comment in axiom audit source')
    return ''.join(result)


def expected_declarations(source: str) -> set[str]:
    declarations = re.findall(
        r'^[ \t]*#print[ \t]+axioms[ \t]+([^\s]+)[ \t]*$',
        without_comments(source), flags=re.M)
    if not declarations:
        raise ValueError('The audit source has no explicit #print axioms declarations')
    if len(declarations) != len(set(declarations)):
        raise ValueError('The audit source contains duplicate declarations')
    return set(declarations)


def check_log(expected: set[str], log: str) -> dict[str, list[str]]:
    log = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', log)
    reports: dict[str, list[str]] = {}
    pattern = (
        r"'([^'\r\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
        r'|does not depend on any axioms)'
    )
    for declaration, raw in re.findall(pattern, log):
        if declaration in reports:
            raise ValueError(f'Duplicate axiom report: {declaration}')
        axioms = [name.strip() for name in raw.split(',') if name.strip()]
        forbidden = set(axioms) - ALLOWED_AXIOMS
        if forbidden:
            raise ValueError(f'Unapproved axioms for {declaration}: {sorted(forbidden)}')
        reports[declaration] = axioms
    if set(reports) != expected:
        raise ValueError(
            f'Axiom inventory mismatch: missing={sorted(expected - reports.keys())}, '
            f'unexpected={sorted(reports.keys() - expected)}')
    return reports


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('audit_source', type=Path)
    parser.add_argument('axiom_log', type=Path)
    parser.add_argument('--json', type=Path, required=True, dest='json_output')
    args = parser.parse_args()
    source = args.audit_source.read_text(encoding='utf-8')
    log = args.axiom_log.read_text(encoding='utf-8')
    reports = check_log(expected_declarations(source), log)
    record = {
        'audit_source': str(args.audit_source),
        'audit_source_sha256': hashlib.sha256(args.audit_source.read_bytes()).hexdigest(),
        'axiom_log_sha256': hashlib.sha256(args.axiom_log.read_bytes()).hexdigest(),
        'allowed_axioms': sorted(ALLOWED_AXIOMS),
        'declarations': reports,
    }
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print(f'PASS: {len(reports)} exact axiom reports; only permitted foundational axioms.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'Axiom check failed: {error}', file=sys.stderr)
        raise SystemExit(1) from error
