#!/usr/bin/env sage -python
import json
from pathlib import Path

R.<phi> = PolynomialRing(QQ)
Q = R.quotient(phi^2 - phi - 1, names='phi')
p = Q.gen()

inv2 = 2 - p
inv3 = 2*p - 3
inv5 = 5*p - 8
expr = 360*inv2 - 2*inv3 + inv5/QQ(243)
target = QQ(176410)/243 - QQ(88447)/243 * p
assert expr == target

K.<sqrt5> = QuadraticField(5)
golden = (1 + sqrt5)/2
expr_golden = 360/golden^2 - 2/golden^3 + 1/(3*golden)^5
assert expr_golden == QQ(264373)/486 - QQ(88447)/486 * sqrt5

payload = {
    'target_phi_basis': str(target),
    'target_sqrt5_basis': str(expr_golden),
    'numeric_alpha_inv': str(expr_golden.n(50)),
    'numeric_alpha': str((1/expr_golden).n(50)),
}

out = Path('/tmp/pellis_golden_alpha_sage.json')
out.write_text(json.dumps(payload, indent=2))
print('SAGE PASS')
print(json.dumps(payload, indent=2))
print(f'artifact={out}')
