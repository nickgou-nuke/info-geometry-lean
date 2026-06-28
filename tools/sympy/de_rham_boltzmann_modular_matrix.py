"""
SymPy finite-dimensional toy model for the bridge
    Q(β) = Tr(exp(-β K))
    d/dβ log Q = - <K>
with K = a σ_x + b σ_z.
"""

import json
import sympy as sp


def main():
    a, b, beta = sp.symbols('a b beta', positive=True, real=True)
    sigma_x = sp.Matrix([[0, 1], [1, 0]])
    sigma_z = sp.Matrix([[1, 0], [0, -1]])
    K = a * sigma_x + b * sigma_z

    r = sp.sqrt(a**2 + b**2)
    Q = 2 * sp.cosh(beta * r)
    dlogQ = sp.diff(sp.log(Q), beta)
    K_expect = -dlogQ

    expected_dlogQ = r * sp.tanh(beta * r)
    checks = {
        "Q_formula": sp.simplify(Q - 2 * sp.cosh(beta * r)) == 0,
        "dlogQ_formula": sp.simplify(dlogQ - expected_dlogQ) == 0,
        "bridge_formula": sp.simplify(dlogQ + K_expect) == 0,
    }

    # numeric matrix confirmation at a concrete point
    subs = {a: sp.Integer(1), b: sp.Integer(2), beta: sp.Rational(1, 2)}
    K_num = sp.Matrix(K.subs(subs))
    evals = list(K_num.eigenvals().keys())
    Q_num = sum(sp.exp(-subs[beta] * ev) for ev in evals)
    dlogQ_num = sp.N(dlogQ.subs(subs))
    K_expect_num = sp.N((-dlogQ).subs(subs))

    result = {
        "checks": checks,
        "Q": str(sp.simplify(Q)),
        "dlogQ": str(sp.simplify(dlogQ)),
        "minus_K_expect": str(sp.simplify(K_expect)),
        "numeric": {
            "Q": str(sp.N(Q_num)),
            "dlogQ": str(dlogQ_num),
            "minus_K_expect": str(K_expect_num),
        },
    }
    print(json.dumps(result, indent=2))
    assert all(checks.values())


if __name__ == "__main__":
    main()
