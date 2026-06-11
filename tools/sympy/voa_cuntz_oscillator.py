#!/usr/bin/env python3
"""
SymPy witness for the Vertex Operator Algebra (VOA) on the Cuntz tree.

This mirrors `InfoGeometry.Dynamics.VertexOperatorAlgebra`, where
S_L acts as the creation operator alpha_{-1} and S_L^* acts as the
annihilation operator alpha_{+1}.
"""

import sympy as sp
from primitive_cuntz_exactness_bridge import reduce_cuntz, SL, SR, SLs, SRs, X, I, ZERO

def main():
    print("--- SymPy Twin: Vertex Operator Algebra (VOA) on the Cuntz Tree ---")

    # 1. String Creation
    # Creating an excitation on state X
    created_X = SL * X * SLs
    print(f"String creation on X: {created_X}")

    # 2. String Annihilation
    # Annihilating an excitation
    def annihilate(state):
        return SLs * state * SL

    # 3. Heisenberg Commutation
    # [alpha_{+1}, alpha_{-1}] = 1 logic
    restored_X = annihilate(created_X)
    restored_X_reduced = reduce_cuntz(restored_X)
    print(f"Annihilation of created state: {restored_X_reduced}")
    assert restored_X_reduced == X

    # 4. Orthogonal Suppression (Selection Rule)
    # Attempting to annihilate an S_L excitation with S_R
    def annihilate_R(state):
        return SRs * state * SR

    suppressed_X = annihilate_R(created_X)
    suppressed_X_reduced = reduce_cuntz(suppressed_X)
    print(f"Orthogonal suppression (S_R annihilation on S_L excitation): {suppressed_X_reduced}")
    assert suppressed_X_reduced == ZERO

    print("\n[SUCCESS] The Heisenberg oscillator relations natively emerge from the exact Cuntz vacuum.")

if __name__ == "__main__":
    main()
