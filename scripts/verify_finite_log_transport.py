"""Exact finite log-coordinate checks; not a substitute for Lean proofs.
Carrier: Fin m -> Real, ordered distance coordinates, mean = sum/m.
The arbitrary-size and L1 minimization results are proved only in Lean.
"""
import json
import sympy as s

def verify():
    checks = {}
    for m in (2, 3, 8, 10):
        x = s.symbols(f'x0:{m}')
        a = s.Symbol('a')
        mean = sum(x) / m
        centered = [v - mean for v in x]
        checks[f'zero_sum_{m}'] = s.simplify(sum(centered)) == 0
        checks[f'channel_cancel_{m}'] = all(s.simplify(a + v - sum(a + w for w in x)/m - z) == 0 for v, z in zip(x, centered))
        checks[f'transport_{m}'] = all(s.simplify(a + v - z - (a + mean)) == 0 for v, z in zip(x, centered))
    assert all(checks.values())
    return {'lean_owner': 'InfoGeometry.Probability.FiniteLogTransport', 'carrier': 'Fin m -> Real', 'basis_order': 'distance index; energies are rows', 'checks': checks, 'scope': 'Finite algebraic instances; no CAS claim about medians or robustness'}

if __name__ == '__main__':
    print(json.dumps(verify(), indent=2, sort_keys=True))
