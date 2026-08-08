"""Finite Weyl/Cramer--Rao rescaling witness.

Checks the theorem-honest finite picture:

    shift * clock = q * clock * shift
    [clock, shift] = (1-q) clock*shift
    h_eff * [clock, shift] = h_eff*(1-q) clock*shift

and the operatorial Dikin/Cramer--Rao phase bit:

    H_Dikin = omega(K^2),   h_eff = 1/H_Dikin,   h_eff * H_Dikin = 1.
"""

from __future__ import annotations

import sympy as sp


def clock_shift_pair(n: int) -> tuple[sp.Matrix, sp.Matrix, sp.Symbol]:
    q = sp.symbols("q")
    clock = sp.diag(*[q ** ((-j) % n) for j in range(n)])
    shift = sp.zeros(n)
    for j in range(n):
        shift[(j + 1) % n, j] = 1
    return clock, shift, q


def reduce_root_unity(expr: sp.Expr, q: sp.Symbol, n: int) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), q)
    modulus = sp.Poly(q**n - 1, q)
    return sp.rem(poly, modulus).as_expr()


def assert_zero_mod_root_unity(name: str, matrix: sp.Matrix, q: sp.Symbol, n: int) -> None:
    simplified = matrix.applyfunc(lambda entry: sp.simplify(reduce_root_unity(entry, q, n)))
    assert simplified == sp.zeros(*simplified.shape), f"{name} failed:\n{simplified}"


def omega_equiprobable(matrix: sp.Matrix) -> sp.Expr:
    n = matrix.rows
    ones = sp.ones(n, 1) / sp.sqrt(n)
    return sp.simplify((ones.T * matrix * ones)[0])


def main() -> None:
    h_eff = sp.symbols("h_eff")

    for n in range(2, 8):
        clock, shift, q = clock_shift_pair(n)
        xp = clock * shift
        px = shift * clock
        comm = xp - px

        assert reduce_root_unity(q**n - 1, q, n) == 0, f"q^N failed for N={n}"
        assert_zero_mod_root_unity(f"Weyl relation N={n}", px - q * xp, q, n)
        assert_zero_mod_root_unity(f"commutator factor N={n}", comm - (1 - q) * xp, q, n)
        assert_zero_mod_root_unity(
            f"rescaled commutator N={n}",
            h_eff * comm - h_eff * (1 - q) * xp,
            q,
            n,
        )

    k = sp.symbols("k", nonzero=True)
    K = sp.diag(k, -k)
    dikin_hessian = sp.simplify(omega_equiprobable(K * K))
    action_quantum = sp.simplify(1 / dikin_hessian)

    assert sp.simplify(omega_equiprobable(K)) == 0, "centered K failed"
    assert sp.simplify(dikin_hessian - k**2) == 0, "Dikin Hessian readout failed"
    assert sp.simplify(action_quantum * dikin_hessian - 1) == 0, "CR action bit failed"

    print("weyl_cramer_rao_rescaling.py: finite Weyl/Dikin rescaling witness passed")


if __name__ == "__main__":
    main()
