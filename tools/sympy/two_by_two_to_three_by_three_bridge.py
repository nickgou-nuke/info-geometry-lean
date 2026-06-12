#!/usr/bin/env python3
"""SymPy twin for `InfoGeometry.Topology.TwoByTwoToThreeByThreeBridge`.

Checks only finite matrix identities:
- the 2x2 Jordan nilpotent embedded as diag(N,0) remains square-zero and nonzero;
- the projective embedding diag(J(lambda),1) decomposes as diag(lambda,lambda,1)+diag(N,0);
- the embedded nilpotent commutes with a diagonal third-root vortex operator.

No physical SU(2)/SU(3), Lorentz, confinement, or LLM theorem is asserted.
"""

import sympy as sp


def main() -> None:
    lam = sp.symbols("lambda")
    omega = sp.exp(2 * sp.pi * sp.I / 3)

    N2 = sp.Matrix([[0, 1], [0, 0]])
    J2 = lam * sp.eye(2) + N2

    def lin_embed(A: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([
            [A[0, 0], A[0, 1], 0],
            [A[1, 0], A[1, 1], 0],
            [0,       0,       0],
        ])

    def proj_embed(A: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([
            [A[0, 0], A[0, 1], 0],
            [A[1, 0], A[1, 1], 0],
            [0,       0,       1],
        ])

    N3 = lin_embed(N2)
    scalar_ext = sp.diag(lam, lam, 1)
    vortex = sp.diag(1, 1, omega)

    square_zero = sp.simplify(N3 * N3) == sp.zeros(3)
    nonzero = N3 != sp.zeros(3)
    deviation = sp.simplify(proj_embed(J2) - scalar_ext - N3) == sp.zeros(3)
    commutes_vortex = sp.simplify(N3 * vortex - vortex * N3) == sp.zeros(3)

    print("=== Finite 2x2-to-3x3 block bridge ===")
    print(f"Embedded nilpotent N3:\n{N3}")
    print(f"N3^2 == 0: {square_zero}")
    print(f"N3 != 0: {nonzero}")
    print(f"projective_embed(J(lambda)) = scalar_ext(lambda) + N3: {deviation}")
    print(f"N3 commutes with diagonal third-root vortex: {commutes_vortex}")

    if square_zero and nonzero and deviation and commutes_vortex:
        print("[SUCCESS] finite block bridge identities verified.")


if __name__ == "__main__":
    main()
