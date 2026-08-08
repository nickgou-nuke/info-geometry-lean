#!/usr/bin/env python3
"""Minimal patch: recheck the weakest bug in witness_log_potential.py.

This inspects the source file for the known Singular-block gap expressions
and reports whether the bug patterns remain or have been fixed.
"""

from pathlib import Path


def main() -> None:
    path = Path('/home/goutev/auto/proofs/witness_log_potential.py')
    if not path.exists():
        raise SystemExit(f'missing file: {path}')

    text = path.read_text()
    checks = {
        'old_bug_gap': 'poly gap = dlnQnum * denom - dQnum',
        'old_triv_err': 'err := Abs(dlnQv - dlnQv)',
    }
    found = {name: pattern in text for name, pattern in checks.items()}
    print(found)
    if any(found.values()):
        raise SystemExit('weakest-link bug still present')
    print('ok')


if __name__ == '__main__':
    main()
