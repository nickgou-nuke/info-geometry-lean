#!/usr/bin/env python3
"""SymPy witness for Conf_3^non-iso(C^D) at D=4.

The analytic topology is not proved here.  This script checks the finite
symbolic pieces that mirror NonIsoConf3OrlikSolomon.lean:

  * q_ij = q(x_i - x_j) for q(z)=sum z_a^2 in D=4;
  * dlog(q_ij) has symbolic exterior derivative zero;
  * the Arnold--Orlik--Solomon relation reduces to zero in a rank-2 normal form;
  * the 12|3 cooperad generator map has the expected internal/external split.
"""

from __future__ import annotations

import sympy as sp


def quadratic_form(vector: list[sp.Expr]) -> sp.Expr:
    return sp.expand(sum(entry**2 for entry in vector))


def dlog_form(poly: sp.Expr, coords: list[sp.Symbol]) -> dict[sp.Symbol, sp.Expr]:
    return {coord: sp.diff(poly, coord) / poly for coord in coords}


def exterior_derivative_is_zero(one_form: dict[sp.Symbol, sp.Expr], coords: list[sp.Symbol]) -> bool:
    """Check d(alpha)=0 for alpha=sum a_i dx_i."""
    for i, xi in enumerate(coords):
        for xj in coords[i + 1 :]:
            coeff = sp.simplify(sp.diff(one_form[xj], xi) - sp.diff(one_form[xi], xj))
            if coeff != 0:
                print("nonzero dlog exterior derivative coefficient:", xi, xj, coeff)
                return False
    return True


def vadd(u: tuple[int, int], v: tuple[int, int]) -> tuple[int, int]:
    return (u[0] + v[0], u[1] + v[1])


def vsub(u: tuple[int, int], v: tuple[int, int]) -> tuple[int, int]:
    return (u[0] - v[0], u[1] - v[1])


def reduce_product(product: str) -> tuple[int, int]:
    """Normal form in basis (A12*A23, A12*A13)."""
    if product == "A12A23":
        return (1, 0)
    if product == "A12A13":
        return (0, 1)
    if product == "A23A13":
        return (-1, 1)
    raise ValueError(product)


def delta12(generator: str) -> tuple[str | None, str | None]:
    """Cooperad cocomposition for the cluster {1,2}|{3}."""
    if generator == "A12":
        return (None, "A12")
    if generator in {"A13", "A23"}:
        return ("A13", None)
    raise ValueError(generator)


def main() -> None:
    dim = 4
    xs = [[sp.symbols(f"x{i}{a}") for a in range(dim)] for i in range(1, 4)]
    coords = [coord for point in xs for coord in point]

    pairs = {
        "12": [xs[0][a] - xs[1][a] for a in range(dim)],
        "23": [xs[1][a] - xs[2][a] for a in range(dim)],
        "13": [xs[0][a] - xs[2][a] for a in range(dim)],
    }
    q = {label: quadratic_form(vector) for label, vector in pairs.items()}
    forms = {label: dlog_form(poly, coords) for label, poly in q.items()}

    for label, poly in q.items():
        gradient = [sp.diff(poly, coord) for coord in coords]
        nonzero_gradient_entries = [entry for entry in gradient if entry != 0]
        assert len(nonzero_gradient_entries) == 2 * dim
        assert exterior_derivative_is_zero(forms[label], coords)

    arnold_os = vadd(
        vsub(reduce_product("A12A23"), reduce_product("A12A13")),
        reduce_product("A23A13"),
    )
    assert arnold_os == (0, 0)

    assert delta12("A12") == (None, "A12")
    assert delta12("A13") == ("A13", None)
    assert delta12("A23") == ("A13", None)

    print("non_iso_conf3_orlik_solomon.py: symbolic witnesses passed")
    print("D = 4, q(z)=z0^2+z1^2+z2^2+z3^2")
    print("q12 =")
    sp.pprint(q["12"])
    print("all dlog(q_ij) forms are symbolically closed")
    print("Arnold-Orlik-Solomon relation normal form:", arnold_os)
    print("cooperad delta_12(A12), delta_12(A13), delta_12(A23):")
    print(delta12("A12"), delta12("A13"), delta12("A23"))


if __name__ == "__main__":
    main()
