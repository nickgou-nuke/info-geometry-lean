#!/usr/bin/env python3
"""SymPy witness for the entropic chiral de Rham dictionary.

This script is a finite audit companion to
`EntropicChiralDeRhamFormalization.lean`.  It checks concrete symbolic shadows
of the dictionary:

* Q as trajectory/incidence potential and S=log(Q);
* dlog(Q) as a closed one-form away from Q=0;
* negative log Jacobian/Radon-Nikodym additivity;
* Itakura-Saito Bregman generator identities;
* triangle Wilson entropy incidence count;
* parabolic forward/backward clock composition;
* determinant-null tripotent tile in the algebra of 2x2 matrices;
* finite modular derivation delta(A)=[K,A].
"""

import sympy as sp


def exterior_derivative_one_form(components, coords):
    """Return coefficients dω_ij = ∂i ωj - ∂j ωi for i<j."""
    return {
        (i, j): sp.simplify(sp.diff(components[j], coords[i]) - sp.diff(components[i], coords[j]))
        for i in range(len(coords))
        for j in range(i + 1, len(coords))
    }


def main() -> None:
    E, px, py, pz = sp.symbols("E p_x p_y p_z", real=True)
    t, s, a, b = sp.symbols("t s a b", real=True)
    x, y, c = sp.symbols("x y c", positive=True)

    coords = [E, px, py, pz]
    Q = E**2 - px**2 - py**2 - pz**2
    entropy = sp.log(Q)
    omega = [sp.diff(entropy, coord) for coord in coords]

    closed = exterior_derivative_one_form(omega, coords)
    assert all(coeff == 0 for coeff in closed.values())

    radial = sp.Matrix(coords)
    dlogQ_on_radial = sp.simplify(sum(radial[i] * omega[i] for i in range(4)))
    assert dlogQ_on_radial == 2

    # Jacobian/RN logarithmic additivity.
    J1 = sp.exp(4 * a * t)
    J2 = sp.exp(4 * b * s)
    assert sp.simplify(sp.log(J1 * J2) - sp.log(J1) - sp.log(J2)) == 0
    assert sp.simplify(-sp.log(J1 * J2) - (-sp.log(J1) - sp.log(J2))) == 0

    rho1, rho2 = sp.symbols("rho_1 rho_2", positive=True)
    assert sp.simplify(-sp.log(rho1 * rho2) - (-sp.log(rho1) - sp.log(rho2))) == 0

    # Scalar Itakura-Saito divergence.
    D_is = x / y - sp.log(x / y) - 1
    D_scaled = (c * x) / (c * y) - sp.log((c * x) / (c * y)) - 1
    assert sp.simplify(D_scaled - D_is) == 0
    assert sp.simplify(D_is.subs(x, y)) == 0

    # Matrix Itakura-Saito diagonal tile.
    q1, q2 = sp.symbols("q_1 q_2", positive=True)
    P = sp.diag(x, y)
    R = sp.diag(q1, q2)
    matrix_is = sp.trace(P * R.inv()) - sp.log((P * R.inv()).det()) - 2
    expected_matrix_is = x / q1 + y / q2 - sp.log(x * y / (q1 * q2)) - 2
    assert sp.simplify(matrix_is - expected_matrix_is) == 0

    # Triangle Wilson entropy count: three oriented unit incidences.
    L12, L23, L31 = 1, 1, 1
    wilson_entropy = L12 + L23 + L31
    assert wilson_entropy == 3

    # Parabolic forward/backward flow, exp(tN)=I+tN for N^2=0.
    N = sp.Matrix([[0, 1], [0, 0]])
    I2 = sp.eye(2)
    P_t = I2 + t * N
    P_s = I2 + s * N
    P_neg_t = I2 - t * N
    assert N**2 == sp.zeros(2)
    assert sp.simplify(P_t * P_s - (I2 + (t + s) * N)) == sp.zeros(2)
    assert sp.simplify(P_t * P_neg_t - I2) == sp.zeros(2)

    # 2x2 determinant-null tripotent tile.
    E00 = sp.Matrix([[1, 0], [0, 0]])
    assert E00.det() == 0
    assert E00**3 == E00

    # Modular derivation in a 2x2 algebra: sigma_eps(A)=exp(eps K) A exp(-eps K).
    k1, k2 = sp.symbols("k1 k2")
    A00, A01, A10, A11 = sp.symbols("A00 A01 A10 A11")
    eps = sp.symbols("eps")
    K = sp.diag(k1, k2)
    A = sp.Matrix([[A00, A01], [A10, A11]])
    expK = sp.diag(sp.exp(eps * k1), sp.exp(eps * k2))
    sigma = expK * A * expK.inv()
    delta = sigma.diff(eps).subs(eps, 0)
    assert sp.simplify(delta - (K * A - A * K)) == sp.zeros(2)

    print("Q =", Q)
    print("S=log(Q) =", entropy)
    print("omega=dlog(Q) =", omega)
    print("d omega coefficients =", closed)
    print("i_radial dlog(Q) =", dlogQ_on_radial)
    print("D_IS scale invariant and zero on diagonal")
    print("matrix D_IS =", matrix_is)
    print("triangle Wilson entropy =", wilson_entropy)
    print("parabolic clocks compose and invert")
    print("E00 determinant-null tripotent verified")
    print("delta(A)=[K,A] verified")
    print("entropic_chiral_derham_formalization.py: finite audit passed")


if __name__ == "__main__":
    main()
