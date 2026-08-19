#!/usr/bin/env python3
"""SymPy audit for Cartan/de Rham chemical-potential g0 bridge.

Audit only: Lean is the proof kernel.  This script verifies the model example
ω=d log Q on the Minkowski/Pauli quadric under a conformal g0 scaling field.
"""

import sympy as sp


def main() -> None:
    E, px, py, pz, c = sp.symbols("E p_x p_y p_z c", real=True)
    P = [E, px, py, pz]

    Q = E**2 - px**2 - py**2 - pz**2
    omega = [sp.diff(sp.log(Q), x) for x in P]

    # Chemical-potential/g0 conformal scaling vector field.
    X = [c * x for x in P]

    # Cartan witness for a closed one-form: L_X ω = d(i_X ω) in cohomology.
    iota = sp.simplify(sum(Xi * wi for Xi, wi in zip(X, omega)))
    d_iota = [sp.simplify(sp.diff(iota, x)) for x in P]

    # Direct coordinate Lie derivative for a 1-form:
    # (L_X ω)_i = X^j ∂_j ω_i + ω_j ∂_i X^j.
    lie = []
    for i, x_i in enumerate(P):
        term = sum(X[j] * sp.diff(omega[i], P[j]) for j in range(4))
        term += sum(omega[j] * sp.diff(X[j], x_i) for j in range(4))
        lie.append(sp.simplify(term))

    assert sp.simplify(iota - 2 * c) == 0
    assert all(comp == 0 for comp in d_iota)
    assert all(comp == 0 for comp in lie)

    # Chemical potential as a 0-form on the triangle: exact edge one-form.
    mu1, mu2, mu3 = sp.symbols("mu_1 mu_2 mu_3", real=True)
    alpha12 = mu2 - mu1
    alpha23 = mu3 - mu2
    alpha31 = mu1 - mu3
    assert sp.simplify(alpha12 + alpha23 + alpha31) == 0

    # Formal mixed Arnold check with commuting symbolic wedge labels: this only
    # records the target relation shape, not an analytic de Rham proof.
    a12, a13, a23, b13, b23 = sp.symbols("a12 a13 a23 b13 b23")
    mixed_relation = a12 * b23 - a12 * b13 + a23 * b13
    beta23_compensation = sp.solve(sp.Eq(mixed_relation, 0), b23)[0]

    # Tolman/Ehrenfest-style normalization audit.  This is a symbolic deferred_interface
    # check: once the geometric comparison supplies g00*mu^2=const, the inverse
    # scaling is algebraically forced.
    mu, kappa = sp.symbols("mu kappa", nonzero=True)
    g00 = kappa / mu**2
    tolman_constant = sp.simplify(g00 * mu**2)
    assert tolman_constant == kappa

    print("Q =", Q)
    print("omega=dlogQ components:")
    for name, comp in zip(["E", "px", "py", "pz"], omega):
        print(f"  omega_{name} = {sp.simplify(comp)}")
    print("i_X omega =", iota)
    print("d(i_X omega) =", d_iota)
    print("direct Lie derivative L_X omega =", lie)
    print("exact triangle alpha12+alpha23+alpha31 =", sp.simplify(alpha12 + alpha23 + alpha31))
    print("mixed Arnold deferred_interface expression =", mixed_relation)
    print("beta23 compensation solving mixed relation =", beta23_compensation)
    print("Tolman deferred_interface normalization g00*mu^2 =", tolman_constant)
    print("chemical_potential_derham_g0_witness.py: finite audit passed")


if __name__ == "__main__":
    main()
