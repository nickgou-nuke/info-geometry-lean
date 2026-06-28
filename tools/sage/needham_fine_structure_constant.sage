#!/usr/bin/env sage -python
import json
from pathlib import Path

K.<sqrt5> = QuadraticField(5)
phi = (1 + sqrt5) / 2
assert phi^2 == phi + 1

RR80 = RealField(80)
pi80 = RR80.pi()
e80 = RR80(exp(1))
phi80 = (RR80(1) + RR80(5).sqrt()) / RR80(2)
expr80 = RR80(10) * pi80 * phi80 * e80 - pi80.log()
codata = RR80('137.035999084')
abs_error = abs(expr80 - codata)
rel_error = abs_error / codata

payload = {
    'phi_numeric_50': str(phi80.n(50)),
    'needham_alpha_inverse_50': str(expr80.n(50)),
    'codata2018_alpha_inverse': str(codata.n(20)),
    'abs_error_50': str(abs_error.n(50)),
    'rel_error_50': str(rel_error.n(50)),
}

out = Path('/tmp/needham_fine_structure_constant_sage.json')
out.write_text(json.dumps(payload, indent=2))
print('SAGE PASS')
print(json.dumps(payload, indent=2))
print(f'artifact={out}')
