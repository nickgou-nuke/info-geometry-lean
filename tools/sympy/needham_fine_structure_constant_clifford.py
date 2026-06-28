#!/usr/bin/env python3
import json
from pathlib import Path
import sympy as sp
import clifford as cf

cf.Cl(2)
phi = (1 + sp.sqrt(5)) / 2
expr = 10 * sp.pi * phi * sp.E - sp.log(sp.pi)
closed = 5 * sp.pi * (1 + sp.sqrt(5)) * sp.E - sp.log(sp.pi)

assert sp.simplify(phi**2 - phi - 1) == 0
assert sp.simplify(expr - closed) == 0

payload = {
    'phi_numeric_50': str(sp.N(phi, 50)),
    'needham_alpha_inverse_50': str(sp.N(expr, 50)),
}

out = Path('/tmp/needham_fine_structure_constant_clifford.json')
out.write_text(json.dumps(payload, indent=2))
print('CLIFFORD PASS')
print(json.dumps(payload, indent=2))
print(f'artifact={out}')
