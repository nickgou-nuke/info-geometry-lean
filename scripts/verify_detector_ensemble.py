"""Exact finite-coordinate checks; Lean owns the general finite proofs.

Carrier: Fin m -> Real, increasing distance index; additive log coordinates.
Transport: ell_i,j - centered(s)_j. No physical time or unit assignment.
"""
import hashlib
import json
import argparse
from pathlib import Path
import sympy as s

checks = {}
for m in (2, 3, 8, 10):
    x = s.symbols(f'x0:{m}', real=True)
    c = s.Symbol('c', real=True)
    mean = sum(x) / m
    centered = [v - mean for v in x]
    checks[f'center_{m}'] = str(s.simplify(sum(centered)))
    checks[f'separable_transport_{m}'] = str(s.simplify(c + x[0] - centered[0] - (c + mean)))
q, wp, wt, b = s.symbols('q wp wt b', positive=True)
checks['angular_recovery'] = str(s.simplify(q * wt / (b*q*wp) - wt/(b*wp)))
assert all(v == '0' for v in checks.values())
packet = {'owner': 'InfoGeometry.Probability.DetectorEnsembleTransport',
 'carrier': 'Fin m -> Real', 'basis_order': 'increasing Fin index',
 'multiplication_convention': 'positive scalar multiplication; log is additive',
 'round_trip': {'log_scales': [0, 2, 4], 'centered': [-2, 0, 2]},
 'round_trip_verified': True,
 'round_trip_lean': 'DetectorEnsembleTransport.lean final finite example',
 'checks': checks, 'sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
args = parser.parse_args()
encoded = json.dumps(packet, indent=2) + '\n'
if args.output:
    args.output.write_text(encoded)
print(encoded, end='')
