#!/usr/bin/env python3
"""Exact SymPy verifier for the finite Ramanujan defect parity tower.

This mirrors `InfoGeometry.Arithmetic.RamanujanDefectTower`.

Only the finite Bernoulli defect polynomial is checked here.  The script does
not claim the analytic Lambert-series/Ramanujan transformation theorem.
"""

from __future__ import annotations

import sympy as sp

from zeta_symmetry_adapted_definitions import ramanujan_rhs_sympy


def assert_symbolic_zero(expr: sp.Expr, label: str) -> None:
    reduced = sp.simplify(expr)
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def finite_defect(n: int, alpha: sp.Expr, beta: sp.Expr) -> sp.Expr:
    """Finite Bernoulli defect with the repository's Ramanujan RHS convention."""
    return sp.factor(ramanujan_rhs_sympy(n, alpha, beta))


def parity_sign(n: int) -> int:
    """The expected swap sign `(-1)^(n+1)`."""
    return -1 if (n + 1) % 2 else 1


def verify_centered_projectors() -> None:
    """Check the algebraic Cartan projectors on an explicit J-even Xi model."""
    u, v = sp.symbols("u v", real=True)
    z = u + sp.I * v

    # Polynomial stand-in for the completed Xi parity law: Xi(z) = Xi(-z).
    xi_even = 1 + z**2 + z**4
    reflected = xi_even.subs(z, -z)

    p_plus = sp.simplify((xi_even + reflected) / 2)
    p_minus = sp.simplify((xi_even - reflected) / 2)

    assert_symbolic_zero(reflected - xi_even, "centered Xi even model")
    assert_symbolic_zero(p_plus - xi_even, "P_J^+(Xi)=Xi model")
    assert_symbolic_zero(p_minus, "P_J^-(Xi)=0 model")


def verify_dirichlet_channel_split() -> None:
    """Verify exp(-(1/2+u+iv)L) factors into ground/dissipation/phase channels."""
    u, v, L = sp.symbols("u v L", real=True)
    mode_exponent = -(sp.Rational(1, 2) + u + sp.I * v) * L
    split_exponent = -sp.Rational(1, 2) * L - u * L - sp.I * v * L
    mode = sp.exp(mode_exponent)
    ground = sp.exp(-sp.Rational(1, 2) * L)
    dissipation = sp.exp(-u * L)
    phase = sp.exp(-sp.I * v * L)

    assert_symbolic_zero(
        sp.expand(mode_exponent - split_exponent),
        "Dirichlet channel exponent split",
    )
    assert_symbolic_zero(
        sp.simplify(mode / (ground * dissipation * phase) - 1),
        "Dirichlet channel multiplicative split",
    )


def verify_alpha_beta_parity() -> list[tuple[int, sp.Expr, int]]:
    alpha, beta = sp.symbols("alpha beta")
    results: list[tuple[int, sp.Expr, int]] = []

    for n in range(1, 5):
        defect = finite_defect(n, alpha, beta)
        sign = parity_sign(n)
        swapped = finite_defect(n, beta, alpha)
        assert_symbolic_zero(
            swapped - sign * defect,
            f"zeta({2 * n + 1}) finite defect alpha/beta parity",
        )
        results.append((n, defect, sign))

    return results


def verify_tau_parity() -> None:
    alpha, beta = sp.symbols("alpha beta")
    tau = sp.symbols("tau", nonzero=True)

    for n in range(1, 5):
        defect = finite_defect(n, alpha, beta)
        tau_defect = sp.factor(defect.subs({alpha: sp.pi * tau, beta: sp.pi / tau}))
        sign = parity_sign(n)
        assert_symbolic_zero(
            tau_defect.subs(tau, 1 / tau) - sign * tau_defect,
            f"zeta({2 * n + 1}) finite defect tau parity",
        )


def main() -> None:
    verify_centered_projectors()
    verify_dirichlet_channel_split()
    results = verify_alpha_beta_parity()
    verify_tau_parity()

    print("RAMANUJAN FINITE DEFECT TOWER -- EXACT SYMPY VERIFIER")
    print("  centered Cartan projectors: P_J^+(Xi)=Xi and P_J^-(Xi)=0 checked")
    print("  Dirichlet channel split: ground*dissipation*phase checked")
    for n, defect, sign in results:
        label = "even" if sign == 1 else "odd"
        print(f"  zeta({2 * n + 1}): sign {sign:+d} ({label})")
        if n in (3, 4):
            print(f"    D_{n}(alpha,beta) = {defect}")
    print("  alpha/beta swap parity checked for n=1..4")
    print("  tau -> 1/tau parity checked for n=1..4")


if __name__ == "__main__":
    main()
