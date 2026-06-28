#!/usr/bin/env python3
import json
from pathlib import Path
import sympy as sp

phi = (1 + sp.sqrt(5)) / 2
expr = 10 * sp.pi * phi * sp.E - sp.log(sp.pi)
closed = 5 * sp.pi * (1 + sp.sqrt(5)) * sp.E - sp.log(sp.pi)
codata = sp.Float('137.035999084', 80)
abs_error = sp.Abs(sp.N(expr, 80) - codata)
rel_error = abs_error / codata

assert sp.simplify(phi**2 - phi - 1) == 0
assert sp.simplify(expr - closed) == 0

payload = {
    'phi_numeric_50': str(sp.N(phi, 50)),
    'needham_alpha_inverse_50': str(sp.N(expr, 50)),
    'codata2018_alpha_inverse': str(codata),
    'abs_error_50': str(sp.N(abs_error, 50)),
    'rel_error_50': str(sp.N(rel_error, 50)),
}

out = Path('/tmp/needham_fine_structure_constant_sympy.json')
out.write_text(json.dumps(payload, indent=2))
print('SYMPY PASS')
print(json.dumps(payload, indent=2))
print(f'artifact={out}')
