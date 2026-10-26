#!/usr/bin/env python3
"""Run independent-core and full-owner checks sequentially; never hide failure."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.quality import check_peirce_reflection as checker

TARGETS = [
    'InfoGeometry.Algebra.CARModuleDecomposition',
    'InfoGeometry.Canonical.PhaseFlowCARBridge',
    'InfoGeometry.Canonical.DoubledCARIntertwiner',
    'InfoGeometry.Canonical.ZornBdGPhaseFlowBridge',
]


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    results = {}
    for label, targets in [('core', TARGETS[:1]), ('integration', TARGETS)]:
        checker.TARGETS = targets
        sys.argv = [sys.argv[0], '--mathlib-root', str(args.mathlib_root),
                    '--output', str(args.output / label)]
        try:
            checker.main()
        except Exception as error:
            results[label] = {'status': 'failed', 'error': str(error)}
            print(label.upper() + ' FAILED: ' + str(error), flush=True)
        else:
            results[label] = {'status': 'passed'}
    passed = all(r['status'] == 'passed' for r in results.values())
    (args.output / 'summary.json').write_text(json.dumps(
        {'passed': passed, 'scopes': results}, indent=2) + '\n')
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
