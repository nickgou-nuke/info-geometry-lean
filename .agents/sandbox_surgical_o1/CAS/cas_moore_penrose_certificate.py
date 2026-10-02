#!/usr/bin/env python3
"""
cas_moore_penrose_certificate.py

Symbolic CAS Certificate Generator for Moore-Penrose Bordered Matrices.
Based on Hartwig (1976), SIAM J. Appl. Math. 31(1), 31-41.

Verifies Moore-Penrose equations and integer-scaled matrix identities for:
1. baseA (2x2)
2. case1Border (3x3)
3. case1Schur (2x2)
4. case3Border (3x3)
5. case3Schur (2x2)
6. borderPermutation (3x3)
7. case1ConjugatedBorder (3x3)

For each pair (A, X) over Q:
- A * X * A = A
- X * A * X = X
- (A * X)^T = A * X
- (X * A)^T = X * A

And integer cleared certificates:
- A = (1 / dA) * M_A
- X = (1 / dX) * M_X
- M_A * M_X * M_A = dA * dX * M_A
- M_X * M_A * M_X = dA * dX * M_X
- (M_A * M_X)^T = M_A * M_X
- (M_X * M_A)^T = M_X * M_A
"""

from __future__ import annotations
import json
import sys
from typing import Any, Dict, List
import sympy as sp

def verify_mp_rational(name: str, A: sp.Matrix, X: sp.Matrix) -> Dict[str, Any]:
    dim_r, dim_c = A.shape
    assert X.shape == (dim_c, dim_r)

    AXA = A * X * A
    XAX = X * A * X
    AX = A * X
    XA = X * A
    AX_star = AX.transpose()
    XA_star = XA.transpose()

    eq1 = (AXA == A)
    eq2 = (XAX == X)
    eq3 = (AX_star == AX)
    eq4 = (XA_star == XA)

    assert eq1, f"Failed eq1 (AXA = A) for {name}"
    assert eq2, f"Failed eq2 (XAX = X) for {name}"
    assert eq3, f"Failed eq3 ((AX)* = AX) for {name}"
    assert eq4, f"Failed eq4 ((XA)* = XA) for {name}"

    # Compute common denominators
    dA = sp.lcm([entry.q for entry in A])
    dX = sp.lcm([entry.q for entry in X])

    M_A = sp.Matrix([[int(entry * dA) for entry in row] for row in A.tolist()])
    M_X = sp.Matrix([[int(entry * dX) for entry in row] for row in X.tolist()])

    scale = dA * dX
    M_AXA = M_A * M_X * M_A
    M_XAX = M_X * M_A * M_X
    M_AX = M_A * M_X
    M_XA = M_X * M_A

    int_eq1 = (M_AXA == scale * M_A)
    int_eq2 = (M_XAX == scale * M_X)
    int_eq3 = (M_AX.transpose() == M_AX)
    int_eq4 = (M_XA.transpose() == M_XA)

    assert int_eq1, f"Failed integer eq1 for {name}"
    assert int_eq2, f"Failed integer eq2 for {name}"
    assert int_eq3, f"Failed integer eq3 for {name}"
    assert int_eq4, f"Failed integer eq4 for {name}"

    def mat_to_list(m: sp.Matrix) -> List[List[Any]]:
        return [[str(m[i, j]) for j in range(m.cols)] for i in range(m.rows)]

    def mat_to_int_list(m: sp.Matrix) -> List[List[int]]:
        return [[int(m[i, j]) for j in range(m.cols)] for i in range(m.rows)]

    return {
        "name": name,
        "rows": dim_r,
        "cols": dim_c,
        "dA": int(dA),
        "dX": int(dX),
        "scale": int(scale),
        "A": mat_to_list(A),
        "X": mat_to_list(X),
        "M_A": mat_to_int_list(M_A),
        "M_X": mat_to_int_list(M_X),
        "AX": mat_to_list(AX),
        "XA": mat_to_list(XA),
        "M_AX": mat_to_int_list(M_AX),
        "M_XA": mat_to_int_list(M_XA),
        "verified_rational_mp": True,
        "verified_integer_cleared": True,
    }

def main():
    print("=" * 70)
    print("CAS Moore-Penrose Certificate Generator (Hartwig 1976 SVD Border)")
    print("=" * 70)

    certs: Dict[str, Any] = {}

    # 1. baseA
    baseA = sp.Matrix([[2, 0], [0, 0]])
    baseAMP = sp.Matrix([[sp.Rational(1, 2), 0], [0, 0]])
    certs["baseA"] = verify_mp_rational("baseA", baseA, baseAMP)

    # 2. case1Border
    case1Border = sp.Matrix([
        [2, 0, 3],
        [0, 0, 0],
        [1, 0, 5]
    ])
    case1BorderMP = sp.Matrix([
        [sp.Rational(5, 7), 0, sp.Rational(-3, 7)],
        [0, 0, 0],
        [sp.Rational(-1, 7), 0, sp.Rational(2, 7)]
    ])
    certs["case1Border"] = verify_mp_rational("case1Border", case1Border, case1BorderMP)

    # 3. case1Schur
    case1Schur = sp.Matrix([
        [sp.Rational(7, 5), 0],
        [0, 0]
    ])
    case1SchurMP = sp.Matrix([
        [sp.Rational(5, 7), 0],
        [0, 0]
    ])
    certs["case1Schur"] = verify_mp_rational("case1Schur", case1Schur, case1SchurMP)

    # 4. case3Border
    case3Border = sp.Matrix([
        [2, 0, 0],
        [0, 0, 1],
        [0, 1, 5]
    ])
    case3BorderMP = sp.Matrix([
        [sp.Rational(1, 2), 0, 0],
        [0, -5, 1],
        [0, 1, 0]
    ])
    certs["case3Border"] = verify_mp_rational("case3Border", case3Border, case3BorderMP)

    # 5. case3Schur
    case3Schur = sp.Matrix([
        [2, 0],
        [0, sp.Rational(-1, 5)]
    ])
    case3SchurMP = sp.Matrix([
        [sp.Rational(1, 2), 0],
        [0, -5]
    ])
    certs["case3Schur"] = verify_mp_rational("case3Schur", case3Schur, case3SchurMP)

    # 6. borderPermutation
    P = sp.Matrix([
        [0, 0, 1],
        [0, 1, 0],
        [1, 0, 0]
    ])
    P_sq = P * P
    P_star = P.transpose()
    assert P_sq == sp.eye(3), "P^2 != 1"
    assert P_star == P, "P* != P"
    certs["borderPermutation"] = {
        "P": [[int(P[i, j]) for j in range(3)] for i in range(3)],
        "P_sq_is_identity": True,
        "P_star_is_self": True
    }

    # 7. case1ConjugatedBorder
    case1ConjA = P * case1Border * P
    case1ConjMP = P * case1BorderMP * P
    certs["case1ConjugatedBorder"] = verify_mp_rational("case1ConjugatedBorder", case1ConjA, case1ConjMP)

    # Output certificates
    json_path = "/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/CAS/moore_penrose_certificates.json"
    with open(json_path, "w") as f:
        json.dump(certs, f, indent=2)
    print(f"Successfully wrote certificates to {json_path}")

    for k, c in certs.items():
        print(f"\n[Packet: {k}]")
        if "dA" in c:
            print(f"  dA={c['dA']}, dX={c['dX']}, scale={c['scale']}")
            print(f"  M_A: {c['M_A']}")
            print(f"  M_X: {c['M_X']}")
            print(f"  M_AX: {c['M_AX']}")
            print(f"  M_XA: {c['M_XA']}")
            print(f"  Rational & Integer Moore-Penrose Laws: VERIFIED")
        else:
            print(f"  P^2 = 1, P* = P : VERIFIED")

    print("\n" + "=" * 70)
    print("ALL 7 MOORE-PENROSE PACKETS SYMBOLICALLY VERIFIED BY SYMPY.")
    print("=" * 70)

if __name__ == "__main__":
    main()
