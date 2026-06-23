#!/usr/bin/env python3
"""
Exact-rational SymPy certificate for the Q8 Schur cover of V4.

This script algebraically verifies the relationship between the Klein four-group (V4)
and the quaternion group (Q8). It constructs the unique 2D complex representation 
of Q8, verifies its defining relations, and proves that it forms a projective 
representation of V4 where the non-trivial Schur multiplier is resolved by 
the central element -I.
"""

import sympy as sp
import sys

def verify_q8_v4_schur_cover():
    print("Verifying Q8 Schur cover of V4 Projective Representation...")

    # 0. Label the eight elements of Q8 by the standard presentation
    q8_elems = ["a0", "a1", "a2", "a3", "xa0", "xa1", "xa2", "xa3"]
    v4_labels = ["I", "W1", "W2", "W12"]

    def q8_mul(x, y):
        # Elements are encoded as a^i and x a^i with i mod 4.
        def parse(z):
            if z.startswith("xa"):
                return (1, int(z[2:]) % 4)
            return (0, int(z[1:]) % 4)

        sx, ix = parse(x)
        sy, iy = parse(y)
        if sx == 0 and sy == 0:
            return f"a{(ix + iy) % 4}"
        if sx == 0 and sy == 1:
            return f"xa{(iy - ix) % 4}"
        if sx == 1 and sy == 0:
            return f"xa{(ix + iy) % 4}"
        return f"a{(2 + iy - ix) % 4}"

    def q8_to_v4(z):
        return {
            "a0": "I",
            "a1": "W1",
            "a2": "I",
            "a3": "W1",
            "xa0": "W2",
            "xa1": "W12",
            "xa2": "W2",
            "xa3": "W12",
        }[z]

    def v4_mul(x, y):
        table = {
            ("I", "I"): "I", ("I", "W1"): "W1", ("I", "W2"): "W2", ("I", "W12"): "W12",
            ("W1", "I"): "W1", ("W2", "I"): "W2", ("W12", "I"): "W12",
            ("W1", "W1"): "I", ("W2", "W2"): "I", ("W12", "W12"): "I",
            ("W1", "W2"): "W12", ("W2", "W1"): "W12",
            ("W1", "W12"): "W2", ("W12", "W1"): "W2",
            ("W2", "W12"): "W1", ("W12", "W2"): "W1",
        }
        return table[(x, y)]

    for x in q8_elems:
        for y in q8_elems:
            lhs = q8_to_v4(q8_mul(x, y))
            rhs = v4_mul(q8_to_v4(x), q8_to_v4(y))
            assert lhs == rhs, (x, y, lhs, rhs)

    assert q8_to_v4("a0") == "I"
    assert q8_to_v4("a2") == "I"
    print("Exact quotient map Q8 -> V4 checks out on all 64 products.")
    
    # 1. Define the 2D irreducible representation of Q8
    I = sp.eye(2)
    # Using sympy imaginary unit I -> sp.I
    i = sp.I
    
    M_i = sp.Matrix([
        [i, 0],
        [0, -i]
    ])
    
    M_j = sp.Matrix([
        [0, 1],
        [-1, 0]
    ])
    
    M_k = sp.Matrix([
        [0, i],
        [i, 0]
    ])
    
    print("\n1. Generators of Q8 in SU(2):")
    print("M_i:")
    sp.pprint(M_i)
    print("M_j:")
    sp.pprint(M_j)
    print("M_k:")
    sp.pprint(M_k)
    
    # 2. Verify Q8 relations: i^2 = j^2 = k^2 = ijk = -1
    print("\n2. Verifying Q8 defining relations...")
    rel1 = M_i**2
    rel2 = M_j**2
    rel3 = M_k**2
    rel4 = M_i * M_j * M_k
    
    assert rel1 == -I, "M_i^2 != -I"
    assert rel2 == -I, "M_j^2 != -I"
    assert rel3 == -I, "M_k^2 != -I"
    assert rel4 == -I, "M_i M_j M_k != -I"
    print("All Q8 relations (M_i^2 = M_j^2 = M_k^2 = M_i M_j M_k = -I) hold EXACTLY.")
    
    # 3. Verify Projective Commutativity (V4 Quotient)
    # In V4, elements commute. In Q8, they anticommute, mapping to the SAME projective class.
    print("\n3. Verifying Projective Commutativity (V4 Projective Representation)...")
    comm_ij = M_i * M_j
    comm_ji = M_j * M_i
    
    sp.pprint(comm_ij)
    sp.pprint(comm_ji)
    
    assert comm_ij == -comm_ji, "Generators do not anticommute!"
    print("M_i * M_j = -M_j * M_i")
    print("This means [M_i, M_j] = 0 in PGL(2, C), providing a projective representation of V4.")
    
    # 4. Central Extension 1 -> Z2 -> Q8 -> V4 -> 1
    # The center of the generated algebra is exactly {I, -I}.
    # Modulo the center, the group generated is isomorphic to V4.
    print("\nThe Schur multiplier H^2(V4, C*) = Z2 is resolved by lifting to Q8.")
    print("JSON_STATUS: SUCCESS")

if __name__ == "__main__":
    verify_q8_v4_schur_cover()
