"""SymPy witness: Fredholm/Cayley regularization of modular Delta.

Regularize the modular operator near the s=0/tripotent defect by
    Delta_reg = (Delta - I)/(Delta + I).
If Delta=e^K, then scalar Delta_reg=tanh(K/2), linear near K=0.
For a biquaternion generator K=v sigma_1, the matrix regularization is
    (e^K-I)(e^K+I)^(-1)=tanh(v/2) sigma_1.
"""

import sympy as sp


def verify_fredholm_regularization():
    K_val = sp.symbols('K_val', real=True)
    Delta = sp.exp(K_val)
    Delta_reg = sp.simplify((Delta - 1) / (Delta + 1))
    expansion = sp.series(Delta_reg, K_val, 0, 5)
    assert sp.simplify(Delta_reg - sp.tanh(K_val/2)) == 0
    assert expansion.removeO().coeff(K_val, 1) == sp.Rational(1, 2)
    assert expansion.removeO().coeff(K_val, 2) == 0

    v = sp.symbols('v', real=True)
    I_mat = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    K_mat = v * s1
    assert K_mat**2 == v**2 * I_mat

    exp_K = sp.cosh(v) * I_mat + sp.sinh(v) * s1
    Delta_reg_mat = sp.simplify((exp_K - I_mat) * (exp_K + I_mat).inv())
    expected = (sp.sinh(v) / (sp.cosh(v) + 1)) * s1
    expected_tanh = sp.tanh(v/2) * s1
    half_diff = (expected - expected_tanh).applyfunc(
        lambda e: sp.simplify(sp.trigsimp(e).rewrite(sp.exp))
    )
    assert half_diff == sp.zeros(2)

    diff = (Delta_reg_mat - expected).applyfunc(lambda e: sp.trigsimp(sp.simplify(e)))
    return {
        "scalar_identity": sp.simplify(Delta_reg - sp.tanh(K_val/2)) == 0,
        "scalar_expansion": expansion,
        "linear_coefficient": expansion.removeO().coeff(K_val, 1),
        "matrix_match": diff == sp.zeros(2),
    }


if __name__ == "__main__":
    results = verify_fredholm_regularization()
    print(results)
    assert results["scalar_identity"]
    assert results["matrix_match"]
    print("fredholm_modular_regularization.py: All identities verified")
