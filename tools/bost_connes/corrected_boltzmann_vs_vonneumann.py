#!/usr/bin/env python3
"""
Theorem-honest local Boltzmann/von Neumann correction packet.

This script verifies only exact scalar formulas for a finite Gibbs ensemble:
- Q(β) = Σ exp(-β E_i)
- S_B(β) = log Q(β)
- <E>(β) = Σ p_i E_i with p_i = exp(-β E_i)/Q(β)
- S_vN(β) = -Σ p_i log p_i = S_B(β) + β <E>(β)

It does not claim a global de Rham/modular/time identification, and it does not
claim that von Neumann entropy is literally an expectation of the Boltzmann
scalar `log Q`.
"""

import sympy as sp


def main() -> None:
    print("=" * 80)
    print("BOLTZMANN vs VON NEUMANN: THEOREM-HONEST LOCAL PACKET")
    print("=" * 80)
    print()

    beta = sp.Symbol("beta", real=True)
    E0, E1 = sp.symbols("E0 E1", real=True)

    Q = sp.exp(-beta * E0) + sp.exp(-beta * E1)
    S_B = sp.log(Q)
    p0 = sp.exp(-beta * E0) / Q
    p1 = sp.exp(-beta * E1) / Q
    avg_E = sp.simplify(p0 * E0 + p1 * E1)
    S_vN = sp.simplify(-(p0 * sp.log(p0) + p1 * sp.log(p1)))

    print("1. Partition function and Boltzmann potential")
    print(f"   Q(β) = {Q}")
    print(f"   S_B(β) = log(Q) = {S_B}")
    print()

    print("2. Gibbs weights and mean energy")
    print(f"   p0 = {sp.simplify(p0)}")
    print(f"   p1 = {sp.simplify(p1)}")
    print(f"   <E> = {avg_E}")
    print()

    print("3. von Neumann entropy")
    print(f"   S_vN = {S_vN}")
    print()

    target_legendre = sp.simplify(S_B + beta * avg_E)
    legendre_gap = sp.simplify(S_vN - target_legendre)
    print("4. Exact local relation")
    print("   Claim: S_vN = S_B + β <E>")
    print(f"   LHS S_vN      = {S_vN}")
    print(f"   RHS S_B+β<E>  = {target_legendre}")
    print(f"   Symbolic check: {sp.Eq(S_vN, target_legendre)}")
    assert legendre_gap == 0
    subs_check = {E0: sp.Integer(1), E1: sp.Integer(3), beta: sp.Integer(2)}
    print(f"   Numeric witness at {subs_check}: LHS = {sp.simplify(S_vN.subs(subs_check))}, RHS = {sp.simplify(target_legendre.subs(subs_check))}")
    print()

    dS_B = sp.simplify(sp.diff(S_B, beta))
    print("5. de Rham/Boltzmann scalar derivative")
    print(f"   d/dβ log(Q) = {dS_B}")
    print("   This is the derivative of the Boltzmann potential, not a global theorem")
    print()

    dS_vN = sp.simplify(sp.diff(S_vN, beta))
    rhs_full = sp.simplify(dS_B + avg_E + beta * sp.diff(avg_E, beta))
    first_law_gap = sp.simplify(dS_vN - rhs_full)
    print("6. Conditional derivative packet")
    print("   Exact identity: dS_vN/dβ = dS_B/dβ + <E> + β d<E>/dβ")
    print(f"   LHS dS_vN/dβ         = {dS_vN}")
    print(f"   RHS full derivative  = {rhs_full}")
    print(f"   Symbolic check: {sp.Eq(dS_vN, rhs_full)}")
    assert first_law_gap == 0
    print(f"   Numeric witness at {subs_check}: LHS = {sp.simplify(dS_vN.subs(subs_check))}, RHS = {sp.simplify(rhs_full.subs(subs_check))}")
    print("   Therefore, if dS_B/dβ = 0, then dS_vN/dβ = <E> + β d<E>/dβ")
    print()

    print("CONCLUSION")
    print("- Verified local scalar packet for a two-level Gibbs ensemble.")
    print("- Verified S_vN = log(Q) + β <E>.")
    print("- No claim here about global de Rham cohomology, modular time, or physical equivalence.")
    print("=" * 80)


if __name__ == "__main__":
    main()
