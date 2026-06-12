#!/usr/bin/env python3
"""Repaired Section 29 finite quantum-effective-action algebra.

Mirrors `InfoGeometry.Physics.Section29QuantumEffectiveAction`.

Checks only finite algebraic consequences:
- formal two-loop expansion and classical limit;
- linear RG running and additive flow law;
- quartic condensate residual critical-point identities;
- superficial degree bookkeeping.

No path integral, Tr log theorem, renormalizability theorem, exact RG theorem,
Hawking-radiation theorem, or black-hole information theorem is asserted.
"""

import sympy as sp


def main() -> None:
    hbar, S, G1, G2 = sp.symbols("hbar S Gamma1 Gamma2")
    Gamma = S + hbar * G1 + hbar**2 * G2

    classical_limit = sp.simplify(Gamma.subs(hbar, 0) - S) == 0
    loop_remainder = sp.simplify((Gamma - S) - (hbar * G1 + hbar**2 * G2)) == 0

    g0, slope, t, s = sp.symbols("g0 slope t s")
    running = lambda u: g0 - slope * u
    flow_law = sp.simplify(running(t + s) - (running(t) - slope * s)) == 0
    fixed_zero_slope = sp.simplify((-slope).subs(slope, 0)) == 0

    a, b, phi = sp.symbols("a b phi")
    V = a * phi**2 + b * phi**4
    residual = sp.diff(V, phi)
    residual_expected = 2 * a * phi + 4 * b * phi**3
    residual_formula = sp.simplify(residual - residual_expected) == 0
    residual_zero_at_origin = sp.simplify(residual_expected.subs(phi, 0)) == 0
    reduced_condition = sp.simplify(residual_expected - 2 * phi * (a + 2 * b * phi**2)) == 0

    Eq, Eg, Epsi, Vint = sp.symbols("E_q E_g E_psi V_int", integer=True)
    degree = 4 - Eq - 2 * Eg - Epsi + Vint
    add_q = sp.simplify((4 - (Eq + 1) - 2 * Eg - Epsi + Vint) - (degree - 1)) == 0
    add_g = sp.simplify((4 - Eq - 2 * (Eg + 1) - Epsi + Vint) - (degree - 2)) == 0
    add_v = sp.simplify((4 - Eq - 2 * Eg - Epsi + (Vint + 1)) - (degree + 1)) == 0

    print("=== Repaired Section 29 finite effective-action algebra ===")
    print(f"classical limit Γ(0)=S: {classical_limit}")
    print(f"loop remainder identity: {loop_remainder}")
    print(f"linear RG additive flow law: {flow_law}")
    print(f"zero slope gives beta=0: {fixed_zero_slope}")
    print(f"quartic residual dV/dphi formula: {residual_formula}")
    print(f"zero condensate residual: {residual_zero_at_origin}")
    print(f"residual factorization 2φ(a+2bφ²): {reduced_condition}")
    print(f"degree shift add quaternion leg: {add_q}")
    print(f"degree shift add graviton leg: {add_g}")
    print(f"degree shift add vertex: {add_v}")

    checks = [
        classical_limit,
        loop_remainder,
        flow_law,
        fixed_zero_slope,
        residual_formula,
        residual_zero_at_origin,
        reduced_condition,
        add_q,
        add_g,
        add_v,
    ]
    if all(checks):
        print("[SUCCESS] repaired finite Section 29 algebraic identities verified.")


if __name__ == "__main__":
    main()
