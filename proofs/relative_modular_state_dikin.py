"""Finite witness for relative modular state readout and Dikin germ.

This mirrors `RelativeModularStateDikin.lean` in a concrete 2x2 matrix model.
The analytic Tomita--Takesaki data are not claimed here; this checks the
finite algebraic state/readout identities:

    omega(OP - I) = c  <=>  omega(OP) = c + 1
    omega(exp_epsK - I - eps*K)
      = eps**2/2 * omega(K**2) + omega(R3)

for a vector state omega(A)=<Omega,A Omega>, with <Omega,Omega>=1.
"""

from __future__ import annotations

import sympy as sp


eps, c = sp.symbols("eps c")
k0, k1 = sp.symbols("k0 k1")
r00, r01, r10, r11 = sp.symbols("r00 r01 r10 r11")
op00, op01, op10, op11 = sp.symbols("op00 op01 op10 op11")

I2 = sp.eye(2)
Omega = sp.Matrix([1, 0])


def omega(matrix: sp.Matrix) -> sp.Expr:
    """Vector state <Omega, A Omega> for Omega=e0."""
    return (Omega.T * matrix * Omega)[0]


def assert_zero(name: str, expr: sp.Expr | sp.Matrix) -> None:
    simplified = sp.simplify(expr)
    if isinstance(simplified, sp.MatrixBase):
        assert simplified == sp.zeros(*simplified.shape), f"{name} failed: {simplified}"
    else:
        assert simplified == 0, f"{name} failed: {simplified}"


OP = sp.Matrix([[op00, op01], [op10, op11]])
K = sp.diag(k0, k1)
R3 = sp.Matrix([[r00, r01], [r10, r11]])

exp_split = I2 + eps * K + (eps**2 / 2) * (K * K) + R3
bregman = exp_split - I2 - eps * K
dikin_quadratic_readout = (eps**2 / 2) * omega(K * K)


def main() -> None:
    assert_zero("vacuum normalization", omega(I2) - 1)

    gauge_left = omega(OP - I2) - c
    gauge_right = omega(OP) - (c + 1)
    assert_zero("gauge equivalence", sp.expand(gauge_left - gauge_right))

    assert_zero(
        "operator bregman split",
        bregman - ((eps**2 / 2) * (K * K) + R3),
    )

    assert_zero(
        "state dikin readout",
        omega(bregman) - (dikin_quadratic_readout + omega(R3)),
    )

    centered_K = K - omega(K) * I2
    centered_exp_split = I2 + eps * centered_K + (eps**2 / 2) * (centered_K * centered_K) + R3
    centered_bregman = centered_exp_split - I2 - eps * centered_K

    assert_zero("centered modular generator", omega(centered_K))
    assert_zero(
        "centered readout has no linear term",
        omega(centered_exp_split - I2) - omega(centered_bregman),
    )

    print("relative modular state/Dikin finite witness passed")


if __name__ == "__main__":
    main()
