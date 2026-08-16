#!/usr/bin/env python3
"""SymPy witness for the conditional Trifactor-Zeta bridge.

Companion to `InfoGeometry.Arithmetic.TrifactorZetaBridge`.

The script checks only the finite algebra:

* a tripotent operator `T^3 = T` has projectors `P0`, `P+`, `P-`;
* `P+ + P- = T^2`;
* if active support `(P+ + P-) rho` vanishes, then `P0 rho = rho`;
* an even centered-xi shadow satisfies `Xi(z) = Xi(-z)`.

It does not claim or numerically test the Riemann Hypothesis.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def assert_expr_eq(name: str, lhs: sp.Expr, rhs: sp.Expr) -> None:
    diff = sp.simplify(lhs - rhs)
    if diff != 0:
        raise AssertionError(f"{name} failed: {diff}")
    print(f"  {name}: OK")


def projectors(op: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    op2 = op * op
    eye = sp.eye(op.rows)
    p_zero = eye - op2
    p_plus = (op2 + op) / 2
    p_minus = (op2 - op) / 2
    return p_zero, p_plus, p_minus


def verify_trifactor_null_state() -> None:
    print("Conditional tripotent null-state bridge")

    T = sp.diag(1, 0, -1)
    P0, Pp, Pm = projectors(T)
    active = Pp + Pm

    a, b, c = sp.symbols("a b c")
    rho = sp.Matrix([a, b, c])

    assert_matrix_eq("T^3 = T", T**3, T)
    assert_matrix_eq("P0 + P+ + P- = I", P0 + Pp + Pm, sp.eye(3))
    assert_matrix_eq("P+ + P- = T^2", active, T**2)

    active_rho = active * rho
    assert_matrix_eq("active support is (a, 0, c)", active_rho, sp.Matrix([a, 0, c]))

    vacuum_rho = rho.subs({a: 0, c: 0})
    assert_matrix_eq("active support vanishes on vacuum rho", active * vacuum_rho, sp.zeros(3, 1))
    assert_matrix_eq("P0 rho = rho under active=0", P0 * vacuum_rho, vacuum_rho)

    # If both active components vanish independently, the same collapse follows.
    assert_matrix_eq("P+ rho = 0 under plus component vanishing", Pp * vacuum_rho, sp.zeros(3, 1))
    assert_matrix_eq("P- rho = 0 under minus component vanishing", Pm * vacuum_rho, sp.zeros(3, 1))


def verify_centered_xi_parity_shadow() -> None:
    print("\nCentered completed-xi parity shadow")
    z, gamma = sp.symbols("z gamma")

    # A symbolic even shadow of the centered completed xi function.
    Xi = z**4 + gamma * z**2
    assert_expr_eq("Xi(z) = Xi(-z)", Xi, Xi.subs(z, -z))

    root = sp.Integer(0)
    assert_expr_eq("zero reflects to zero", Xi.subs(z, root), Xi.subs(z, -root))


def main() -> None:
    print("=" * 72)
    print("TRIFACTOR-ZETA BRIDGE WITNESS")
    print("=" * 72)
    verify_trifactor_null_state()
    verify_centered_xi_parity_shadow()
    print("\nAll Trifactor-Zeta bridge witness checks passed.")


if __name__ == "__main__":
    main()

