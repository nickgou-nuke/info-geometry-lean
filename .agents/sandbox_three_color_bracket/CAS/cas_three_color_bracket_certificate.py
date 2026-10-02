#!/usr/bin/env python3
"""
cas_three_color_bracket_certificate.py

Symbolic CAS Certificate Generator and Verifier for the Split-Octonion
Three-Colour Native Bracket Table (24 Commutators and Anticommutators over ℚ).

This script computes and independently certifies all 24 theorems in:
  lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean

It verifies both:
1. Cayley-Dickson doubling multiplication on ℚ^8 (the native representation in Lean).
2. Zorn vector matrix algebra M_2(ℚ, ℚ^3) (the nonassociative matrix representation).
"""

from __future__ import annotations
import json
import sys
from typing import Any, Dict, List, Tuple
from sympy import Rational

BASIS_NAMES = ["one", "l", "i", "il", "j", "jl", "k", "kl"]

def quat_mul(p: Tuple[Rational, ...], q: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    p0, p1, p2, p3 = p
    q0, q1, q2, q3 = q
    return (
        p0*q0 - p1*q1 - p2*q2 - p3*q3,
        p0*q1 + p1*q0 + p2*q3 - p3*q2,
        p0*q2 - p1*q3 + p2*q0 + p3*q1,
        p0*q3 + p1*q2 - p2*q1 + p3*q0
    )

def quat_conj(q: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return (q[0], -q[1], -q[2], -q[3])

def quat_add(p: Tuple[Rational, ...], q: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return (p[0] + q[0], p[1] + q[1], p[2] + q[2], p[3] + q[3])

def oct_mul(x: Tuple[Rational, ...], y: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    q = (x[0], x[2], x[4], x[6])
    r = (x[1], x[3], x[5], x[7])
    s = (y[0], y[2], y[4], y[6])
    t = (y[1], y[3], y[5], y[7])
    left = quat_add(quat_mul(q, s), quat_mul(quat_conj(t), r))
    right = quat_add(quat_mul(t, q), quat_mul(r, quat_conj(s)))
    return (left[0], right[0], left[1], right[1], left[2], right[2], left[3], right[3])

def oct_add(x: Tuple[Rational, ...], y: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return tuple(a + b for a, b in zip(x, y))

def oct_sub(x: Tuple[Rational, ...], y: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return tuple(a - b for a, b in zip(x, y))

def oct_smul(c: Any, x: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    r = Rational(c)
    return tuple(r * a for a in x)

def oct_neg(x: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return tuple(-a for a in x)

def native_comm(x: Tuple[Rational, ...], y: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return oct_sub(oct_mul(x, y), oct_mul(y, x))

def native_anticomm(x: Tuple[Rational, ...], y: Tuple[Rational, ...]) -> Tuple[Rational, ...]:
    return oct_add(oct_mul(x, y), oct_mul(y, x))

class ZornMatrix:
    def __init__(self, a: Rational, v: Tuple[Rational, Rational, Rational],
                 w: Tuple[Rational, Rational, Rational], b: Rational):
        self.a = Rational(a)
        self.v = tuple(Rational(x) for x in v)
        self.w = tuple(Rational(x) for x in w)
        self.b = Rational(b)

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, ZornMatrix):
            return False
        return (self.a == other.a and self.v == other.v and
                self.w == other.w and self.b == other.b)

    def __repr__(self) -> str:
        return f"Zorn(a={self.a}, v={self.v}, w={self.w}, b={self.b})"

def zorn_dot(x: Tuple[Rational, Rational, Rational], y: Tuple[Rational, Rational, Rational]) -> Rational:
    return sum((xi * yi for xi, yi in zip(x, y)), Rational(0))

def zorn_cross(x: Tuple[Rational, Rational, Rational], y: Tuple[Rational, Rational, Rational]) -> Tuple[Rational, Rational, Rational]:
    return (
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0]
    )

def zorn_mul(X: ZornMatrix, Y: ZornMatrix) -> ZornMatrix:
    a_new = X.a * Y.a + zorn_dot(X.v, Y.w)
    v_cross = zorn_cross(X.w, Y.w)
    v_new = tuple(X.a * Y.v[i] + Y.b * X.v[i] - v_cross[i] for i in range(3))
    w_cross = zorn_cross(X.v, Y.v)
    w_new = tuple(Y.a * X.w[i] + X.b * Y.w[i] + w_cross[i] for i in range(3))
    b_new = zorn_dot(X.w, Y.v) + X.b * Y.b
    return ZornMatrix(a_new, v_new, w_new, b_new)

def to_zorn(x: Tuple[Rational, ...]) -> ZornMatrix:
    a = x[0] + x[1]
    b = x[0] - x[1]
    v = (x[2] - x[3], -x[4] + x[5], x[6] - x[7])
    w = (-x[2] - x[3], x[4] + x[5], -x[6] - x[7])
    return ZornMatrix(a, v, w, b)

def generate_certificate() -> Dict[str, Any]:
    zero = (Rational(0),)*8
    one  = (Rational(1), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0))
    l    = (Rational(0), Rational(1), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0))
    i    = (Rational(0), Rational(0), Rational(1), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0))
    il   = (Rational(0), Rational(0), Rational(0), Rational(1), Rational(0), Rational(0), Rational(0), Rational(0))
    j    = (Rational(0), Rational(0), Rational(0), Rational(0), Rational(1), Rational(0), Rational(0), Rational(0))
    jl   = (Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(1), Rational(0), Rational(0))
    k    = (Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(1), Rational(0))
    kl   = (Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(0), Rational(1))

    half = Rational(1, 2)
    N_plus = oct_smul(half, oct_add(one, l))
    N_minus = oct_smul(half, oct_sub(one, l))
    fund_symm = l

    colour_unit = {'red': i, 'green': j, 'blue': k}
    colour_lunit = {'red': il, 'green': jl, 'blue': kl}

    modular_j = {c: oct_neg(oct_mul(fund_symm, colour_unit[c])) for c in ['red', 'green', 'blue']}
    phase_axis = colour_unit

    for c in ['red', 'green', 'blue']:
        assert modular_j[c] == colour_lunit[c], f"modularJ[{c}] != colourLUnit[{c}]"

    sigma_plus = {c: oct_smul(half, oct_sub(modular_j[c], phase_axis[c])) for c in ['red', 'green', 'blue']}
    sigma_minus = {c: oct_smul(half, oct_add(modular_j[c], phase_axis[c])) for c in ['red', 'green', 'blue']}

    colors = ['red', 'green', 'blue']

    # Check Zorn homomorphism
    all_elements = [N_plus, N_minus] + list(sigma_plus.values()) + list(sigma_minus.values())
    for x in all_elements:
        for y in all_elements:
            assert to_zorn(oct_mul(x, y)) == zorn_mul(to_zorn(x), to_zorn(y)), "Zorn homomorphism check failed"

    theorems = {}

    # 1. nativeAnticommutator_sigmaPlus_sigmaPlus
    t1_pairs = {}
    for c in colors:
        for d in colors:
            val = native_anticomm(sigma_plus[c], sigma_plus[d])
            assert val == zero
            t1_pairs[f"{c}_{d}"] = [str(v) for v in val]
    theorems["nativeAnticommutator_sigmaPlus_sigmaPlus"] = {
        "statement": "∀ c d, nativeAnticommutator (modularSigmaPlus c) (modularSigmaPlus d) = 0",
        "verified": True,
        "evaluations": t1_pairs
    }

    # 2. nativeAnticommutator_sigmaMinus_sigmaMinus
    t2_pairs = {}
    for c in colors:
        for d in colors:
            val = native_anticomm(sigma_minus[c], sigma_minus[d])
            assert val == zero
            t2_pairs[f"{c}_{d}"] = [str(v) for v in val]
    theorems["nativeAnticommutator_sigmaMinus_sigmaMinus"] = {
        "statement": "∀ c d, nativeAnticommutator (modularSigmaMinus c) (modularSigmaMinus d) = 0",
        "verified": True,
        "evaluations": t2_pairs
    }

    # 3. nativeSigmaPlus_red_green_commutator
    v3 = native_comm(sigma_plus['red'], sigma_plus['green'])
    rhs3 = oct_smul(2, sigma_minus['blue'])
    assert v3 == rhs3
    theorems["nativeSigmaPlus_red_green_commutator"] = {
        "statement": "nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .green) = (2 : ℚ) • modularSigmaMinus .blue",
        "verified": True,
        "computed": [str(v) for v in v3],
        "expected": [str(v) for v in rhs3]
    }

    # 4. nativeSigmaPlus_red_blue_commutator
    v4 = native_comm(sigma_plus['red'], sigma_plus['blue'])
    rhs4 = oct_smul(-2, sigma_minus['green'])
    assert v4 == rhs4
    theorems["nativeSigmaPlus_red_blue_commutator"] = {
        "statement": "nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .blue) = (-2 : ℚ) • modularSigmaMinus .green",
        "verified": True,
        "computed": [str(v) for v in v4],
        "expected": [str(v) for v in rhs4]
    }

    # 5. nativeSigmaPlus_green_blue_commutator
    v5 = native_comm(sigma_plus['green'], sigma_plus['blue'])
    rhs5 = oct_smul(2, sigma_minus['red'])
    assert v5 == rhs5
    theorems["nativeSigmaPlus_green_blue_commutator"] = {
        "statement": "nativeCommutator (modularSigmaPlus .green) (modularSigmaPlus .blue) = (2 : ℚ) • modularSigmaMinus .red",
        "verified": True,
        "computed": [str(v) for v in v5],
        "expected": [str(v) for v in rhs5]
    }

    # 6. nativeSigmaMinus_red_green_commutator
    v6 = native_comm(sigma_minus['red'], sigma_minus['green'])
    rhs6 = oct_smul(-2, sigma_plus['blue'])
    assert v6 == rhs6
    theorems["nativeSigmaMinus_red_green_commutator"] = {
        "statement": "nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .green) = (-2 : ℚ) • modularSigmaPlus .blue",
        "verified": True,
        "computed": [str(v) for v in v6],
        "expected": [str(v) for v in rhs6]
    }

    # 7. nativeSigmaMinus_red_blue_commutator
    v7 = native_comm(sigma_minus['red'], sigma_minus['blue'])
    rhs7 = oct_smul(2, sigma_plus['green'])
    assert v7 == rhs7
    theorems["nativeSigmaMinus_red_blue_commutator"] = {
        "statement": "nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .blue) = (2 : ℚ) • modularSigmaPlus .green",
        "verified": True,
        "computed": [str(v) for v in v7],
        "expected": [str(v) for v in rhs7]
    }

    # 8. nativeSigmaMinus_green_blue_commutator
    v8 = native_comm(sigma_minus['green'], sigma_minus['blue'])
    rhs8 = oct_smul(-2, sigma_plus['red'])
    assert v8 == rhs8
    theorems["nativeSigmaMinus_green_blue_commutator"] = {
        "statement": "nativeCommutator (modularSigmaMinus .green) (modularSigmaMinus .blue) = (-2 : ℚ) • modularSigmaPlus .red",
        "verified": True,
        "computed": [str(v) for v in v8],
        "expected": [str(v) for v in rhs8]
    }

    # 9. nativeSigmaPlusSigmaMinus_commutator
    t9_pairs = {}
    for c in colors:
        for d in colors:
            val = native_comm(sigma_plus[c], sigma_minus[d])
            expected = fund_symm if c == d else zero
            assert val == expected
            t9_pairs[f"{c}_{d}"] = [str(v) for v in val]
    theorems["nativeSigmaPlusSigmaMinus_commutator"] = {
        "statement": "∀ c d, nativeCommutator (modularSigmaPlus c) (modularSigmaMinus d) = if c = d then fundamentalSymmetry else 0",
        "verified": True,
        "evaluations": t9_pairs
    }

    # 10. nativeSigmaPlusSigmaMinus_anticommutator
    t10_pairs = {}
    for c in colors:
        for d in colors:
            val = native_anticomm(sigma_plus[c], sigma_minus[d])
            expected = one if c == d else zero
            assert val == expected
            t10_pairs[f"{c}_{d}"] = [str(v) for v in val]
    theorems["nativeSigmaPlusSigmaMinus_anticommutator"] = {
        "statement": "∀ c d, nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus d) = if c = d then rationalBasis .one else 0",
        "verified": True,
        "evaluations": t10_pairs
    }

    # 11. nativeNPlus_sigmaPlus_commutator
    t11_vals = {}
    for c in colors:
        val = native_comm(N_plus, sigma_plus[c])
        assert val == sigma_plus[c]
        t11_vals[c] = [str(v) for v in val]
    theorems["nativeNPlus_sigmaPlus_commutator"] = {
        "statement": "∀ c, nativeCommutator modularNPlus (modularSigmaPlus c) = modularSigmaPlus c",
        "verified": True,
        "evaluations": t11_vals
    }

    # 12. nativeNPlus_sigmaPlus_anticommutator
    t12_vals = {}
    for c in colors:
        val = native_anticomm(N_plus, sigma_plus[c])
        assert val == sigma_plus[c]
        t12_vals[c] = [str(v) for v in val]
    theorems["nativeNPlus_sigmaPlus_anticommutator"] = {
        "statement": "∀ c, nativeAnticommutator modularNPlus (modularSigmaPlus c) = modularSigmaPlus c",
        "verified": True,
        "evaluations": t12_vals
    }

    # 13. nativeNMinus_sigmaPlus_commutator
    t13_vals = {}
    for c in colors:
        val = native_comm(N_minus, sigma_plus[c])
        assert val == oct_neg(sigma_plus[c])
        t13_vals[c] = [str(v) for v in val]
    theorems["nativeNMinus_sigmaPlus_commutator"] = {
        "statement": "∀ c, nativeCommutator modularNMinus (modularSigmaPlus c) = -modularSigmaPlus c",
        "verified": True,
        "evaluations": t13_vals
    }

    # 14. nativeNMinus_sigmaPlus_anticommutator
    t14_vals = {}
    for c in colors:
        val = native_anticomm(N_minus, sigma_plus[c])
        assert val == sigma_plus[c]
        t14_vals[c] = [str(v) for v in val]
    theorems["nativeNMinus_sigmaPlus_anticommutator"] = {
        "statement": "∀ c, nativeAnticommutator modularNMinus (modularSigmaPlus c) = modularSigmaPlus c",
        "verified": True,
        "evaluations": t14_vals
    }

    # 15. nativeNPlus_sigmaMinus_commutator
    t15_vals = {}
    for c in colors:
        val = native_comm(N_plus, sigma_minus[c])
        assert val == oct_neg(sigma_minus[c])
        t15_vals[c] = [str(v) for v in val]
    theorems["nativeNPlus_sigmaMinus_commutator"] = {
        "statement": "∀ c, nativeCommutator modularNPlus (modularSigmaMinus c) = -modularSigmaMinus c",
        "verified": True,
        "evaluations": t15_vals
    }

    # 16. nativeNPlus_sigmaMinus_anticommutator
    t16_vals = {}
    for c in colors:
        val = native_anticomm(N_plus, sigma_minus[c])
        assert val == sigma_minus[c]
        t16_vals[c] = [str(v) for v in val]
    theorems["nativeNPlus_sigmaMinus_anticommutator"] = {
        "statement": "∀ c, nativeAnticommutator modularNPlus (modularSigmaMinus c) = modularSigmaMinus c",
        "verified": True,
        "evaluations": t16_vals
    }

    # 17. nativeNMinus_sigmaMinus_commutator
    t17_vals = {}
    for c in colors:
        val = native_comm(N_minus, sigma_minus[c])
        assert val == sigma_minus[c]
        t17_vals[c] = [str(v) for v in val]
    theorems["nativeNMinus_sigmaMinus_commutator"] = {
        "statement": "∀ c, nativeCommutator modularNMinus (modularSigmaMinus c) = modularSigmaMinus c",
        "verified": True,
        "evaluations": t17_vals
    }

    # 18. nativeNMinus_sigmaMinus_anticommutator
    t18_vals = {}
    for c in colors:
        val = native_anticomm(N_minus, sigma_minus[c])
        assert val == sigma_minus[c]
        t18_vals[c] = [str(v) for v in val]
    theorems["nativeNMinus_sigmaMinus_anticommutator"] = {
        "statement": "∀ c, nativeAnticommutator modularNMinus (modularSigmaMinus c) = modularSigmaMinus c",
        "verified": True,
        "evaluations": t18_vals
    }

    # 19. nativeNPlus_NMinus_commutator
    v19 = native_comm(N_plus, N_minus)
    assert v19 == zero
    theorems["nativeNPlus_NMinus_commutator"] = {
        "statement": "nativeCommutator modularNPlus modularNMinus = 0",
        "verified": True,
        "computed": [str(v) for v in v19]
    }

    # 20. nativeNPlus_NMinus_anticommutator
    v20 = native_anticomm(N_plus, N_minus)
    assert v20 == zero
    theorems["nativeNPlus_NMinus_anticommutator"] = {
        "statement": "nativeAnticommutator modularNPlus modularNMinus = 0",
        "verified": True,
        "computed": [str(v) for v in v20]
    }

    # 21. nativeNPlus_self_commutator
    v21 = native_comm(N_plus, N_plus)
    assert v21 == zero
    theorems["nativeNPlus_self_commutator"] = {
        "statement": "nativeCommutator modularNPlus modularNPlus = 0",
        "verified": True,
        "computed": [str(v) for v in v21]
    }

    # 22. nativeNPlus_self_anticommutator
    v22 = native_anticomm(N_plus, N_plus)
    rhs22 = oct_smul(2, N_plus)
    assert v22 == rhs22
    theorems["nativeNPlus_self_anticommutator"] = {
        "statement": "nativeAnticommutator modularNPlus modularNPlus = (2 : ℚ) • modularNPlus",
        "verified": True,
        "computed": [str(v) for v in v22],
        "expected": [str(v) for v in rhs22]
    }

    # 23. nativeNMinus_self_commutator
    v23 = native_comm(N_minus, N_minus)
    assert v23 == zero
    theorems["nativeNMinus_self_commutator"] = {
        "statement": "nativeCommutator modularNMinus modularNMinus = 0",
        "verified": True,
        "computed": [str(v) for v in v23]
    }

    # 24. nativeNMinus_self_anticommutator
    v24 = native_anticomm(N_minus, N_minus)
    rhs24 = oct_smul(2, N_minus)
    assert v24 == rhs24
    theorems["nativeNMinus_self_anticommutator"] = {
        "statement": "nativeAnticommutator modularNMinus modularNMinus = (2 : ℚ) • modularNMinus",
        "verified": True,
        "computed": [str(v) for v in v24],
        "expected": [str(v) for v in rhs24]
    }

    generator_coords = {
        "NPlus": [str(x) for x in N_plus],
        "NMinus": [str(x) for x in N_minus],
        "fundamentalSymmetry": [str(x) for x in fund_symm],
        "sigmaPlus": {c: [str(x) for x in sigma_plus[c]] for c in colors},
        "sigmaMinus": {c: [str(x) for x in sigma_minus[c]] for c in colors}
    }

    return {
        "module": "InfoGeometry.Canonical.ThreeColorNativeBracketTable",
        "totalTheorems": len(theorems),
        "allVerified": True,
        "basis": BASIS_NAMES,
        "generators": generator_coords,
        "theorems": theorems
    }

def main():
    cert = generate_certificate()
    print("=" * 70)
    print("  CAS THREE-COLOUR SPLIT-OCTONION BRACKET CERTIFICATE PACKET")
    print("=" * 70)
    print(f"Module: {cert['module']}")
    print(f"Total Bracket Theorems Verified: {cert['totalTheorems']}/24")
    print(f"Status: {'ALL PASS' if cert['allVerified'] else 'FAIL'}")
    print("-" * 70)
    for name, data in cert["theorems"].items():
        print(f" [PASS] {name}")
    print("=" * 70)

    if "--json" in sys.argv:
        print(json.dumps(cert, indent=2))

if __name__ == "__main__":
    main()
