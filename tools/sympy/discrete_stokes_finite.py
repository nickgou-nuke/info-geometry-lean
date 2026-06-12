"""Finite oriented-triangle Stokes mirror.

This mirrors `InfoGeometry.Canonical.DiscreteStokesFinite`.

Closed scope:
* edge order `(01, 12, 02)`;
* `d1(a) = a01 + a12 - a02`;
* finite Stokes on one triangle;
* `d1(d0(f)) = 0`;
* boundary of boundary is zero.

No smooth differential forms, de Rham cohomology, characteristic classes,
instantons, or physical topological charges are claimed here.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Matrix | sp.Expr, label: str) -> None:
    simplified = sp.simplify(expr)
    if isinstance(simplified, sp.MatrixBase):
        ok = simplified == sp.zeros(*simplified.shape)
    else:
        ok = simplified == 0
    if not ok:
        raise AssertionError(f"{label} did not simplify to zero:\n{simplified}")


def main() -> None:
    f0, f1, f2 = sp.symbols("f0 f1 f2")
    a01, a12, a02 = sp.symbols("a01 a12 a02")
    t = sp.symbols("t")

    d0 = sp.Matrix([f1 - f0, f2 - f1, f2 - f0])
    a = sp.Matrix([a01, a12, a02])

    def d1(one_cochain: sp.Matrix) -> sp.Expr:
        return one_cochain[0] + one_cochain[1] - one_cochain[2]

    boundary_integral = a01 + a12 - a02
    bulk_integral = d1(a)
    assert_zero(bulk_integral - boundary_integral, "finite Stokes")
    assert_zero(d1(d0), "d1(d0)=0")

    boundary2 = sp.Matrix([t, t, -t])
    boundary1_matrix = sp.Matrix(
        [
            [-1, 0, -1],
            [1, -1, 0],
            [0, 1, 1],
        ]
    )
    assert_zero(boundary1_matrix * boundary2, "boundary of boundary")

    print("discrete_stokes_finite: ok")
    print("  finite Stokes on oriented triangle [012]")
    print("  d1(d0)=0 and boundary1(boundary2)=0")
    print("  honest scope: finite cochain/chain algebra only")


if __name__ == "__main__":
    main()
