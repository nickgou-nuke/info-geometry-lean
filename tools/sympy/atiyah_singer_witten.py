#!/usr/bin/env python3
"""Finite Atiyah-Singer/Witten index witness.

This script mirrors the Lean module
`InfoGeometry.Canonical.AtiyahSingerWittenIndexBridge`.

It verifies the finite doubled `4 + 4` matrix calculation:

    Tr((-1)^F) = 4 - 4 = 0.

The result is a finite beta-zero Witten-index readout.  It is not, by itself,
a proof of a continuum Atiyah-Singer theorem or a supersymmetry-breaking claim.
"""

import sympy as sp


def main():
    # Define Cuntz dimension N=4, doubled space 8x8.
    N = 4

    # Left shift operator S_L
    S_L = sp.zeros(N)
    for i in range(N - 1):
        S_L[i, i+1] = 1

    # Extended to 8x8
    S_L_doubled = sp.Matrix(
        sp.BlockMatrix([[S_L, sp.zeros(N)], [sp.zeros(N), sp.zeros(N)]])
    )

    # Modular Conjugation J (exchange)
    I = sp.eye(N)
    J = sp.Matrix(sp.BlockMatrix([[sp.zeros(N), I], [I, sp.zeros(N)]]))

    # Grading operator (-1)^F (Bosonic/Fermionic Parity)
    # Physical sector is Bosonic (+1), Ghost sector is Fermionic (-1)
    epsilon = sp.Matrix(sp.BlockMatrix([[I, sp.zeros(N)], [sp.zeros(N), -I]]))

    expected_epsilon = sp.diag(1, 1, 1, 1, -1, -1, -1, -1)
    assert epsilon == expected_epsilon

    print("Grading Operator (-1)^F:")
    sp.pprint(epsilon)

    # Discrete Supercharge Q = D = S_L + J S_L J
    J_SL_J = J * S_L_doubled * J
    Q = S_L_doubled + J_SL_J

    print("\nDiscrete Supercharge Q = D:")
    sp.pprint(Q)

    # Finite Hamiltonian readout H = Q^2.
    H = Q * Q

    print("\nHamiltonian H = Q^2:")
    sp.pprint(H)

    # Witten Index n_0 = Supertrace(e^{-beta H}) = Tr(epsilon * e^{-beta H}).
    # The Lean theorem owns the beta-zero finite trace.
    beta = sp.symbols('beta', real=True, positive=True)

    Witten_Index_beta_0 = sp.trace(epsilon * sp.eye(2*N))
    assert Witten_Index_beta_0 == 0

    print("\nWitten Index n_0 (at beta=0):")
    sp.pprint(Witten_Index_beta_0)

    # Symbolic heat readout for this finite nilpotent shift model.
    exp_neg_beta_H = sp.exp(-beta * H)
    Witten_Index_beta = sp.simplify(sp.trace(epsilon * exp_neg_beta_H))
    assert Witten_Index_beta == 0

    print("\nWitten Index n_0 (for general beta):")
    sp.pprint(Witten_Index_beta)

    print("\nVerified finite readout:")
    print("  Tr((-1)^F) = 4 - 4 = 0")
    print("  Any topological index identified with this finite readout is zero.")


if __name__ == "__main__":
    main()
