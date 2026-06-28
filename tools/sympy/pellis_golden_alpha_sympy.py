#!/usr/bin/env python3
import json
from pathlib import Path
import sympy as sp

phi = sp.Symbol('phi')
expr = 360*phi**-2 - 2*phi**-3 + (3*phi)**-5
relation = phi**2 - phi - 1

# Derived inverse-power identities from phi^2 = phi + 1
inv1 = phi - 1
inv2 = 2 - phi
inv3 = 2*phi - 3
inv4 = 5 - 3*phi
inv5 = 5*phi - 8

expr_reduced = sp.expand(360*inv2 - 2*inv3 + inv5/243)
target = sp.Rational(176410, 243) - sp.Rational(88447, 243)*phi

sqrt5 = sp.sqrt(5)
golden = (1 + sqrt5)/2
expr_golden = sp.simplify(expr.subs(phi, golden))
target_golden = sp.simplify(target.subs(phi, golden))
normal_form = sp.simplify(sp.expand(expr_golden.rewrite(sp.sqrt)))

assert sp.expand(expr_reduced - target) == 0
assert sp.simplify(expr_golden - target_golden) == 0

payload = {
    'relation': 'phi^2 = phi + 1',
    'inverse_powers': {
        'phi^-1': str(inv1),
        'phi^-2': str(inv2),
        'phi^-3': str(inv3),
        'phi^-4': str(inv4),
        'phi^-5': str(inv5),
    },
    'target_phi_basis': str(target),
    'target_sqrt5_basis': str(normal_form),
    'numeric_alpha_inv': str(sp.N(expr_golden, 50)),
    'numeric_alpha': str(sp.N(1/expr_golden, 50)),
}

out = Path('/tmp/pellis_golden_alpha_sympy.json')
out.write_text(json.dumps(payload, indent=2))
print('SYMpy PASS')
print(json.dumps(payload, indent=2))
print(f'artifact={out}')
