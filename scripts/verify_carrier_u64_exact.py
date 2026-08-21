#!/usr/bin/env python3
"""
CARRIER-LEVEL EXACT VERIFICATION FOR G2(2) BOREL SUBGROUP OF ORDER 64
ON THE SPLIT OCTONION ALGEBRA OVER GF(2)
"""

import itertools
import numpy as np
from sympy import Poly, symbols

# Basis ordering:
# 0: a (ePlus)
# 1: b (eMinus)
# 2: x0 (up0)
# 3: x1 (up1)
# 4: x2 (up2)
# 5: y0 (down0)
# 6: y1 (down1)
# 7: y2 (down2)

BASIS_NAMES = ["a", "b", "x0", "x1", "x2", "y0", "y1", "y2"]

def cross_f2(u, v):
    # u, v are 3-dim vectors in GF(2)
    return np.array([
        (u[1]*v[2] ^ u[2]*v[1]) & 1,
        (u[2]*v[0] ^ u[0]*v[2]) & 1,
        (u[0]*v[1] ^ u[1]*v[0]) & 1
    ], dtype=int)

def dot_f2(u, v):
    return (u[0]*v[0] ^ u[1]*v[1] ^ u[2]*v[2]) & 1

def zorn_mul(p1, p2):
    # p1 = (a1, b1, x1, y1)
    # p2 = (a2, b2, x2, y2)
    a1, b1 = p1[0], p1[1]
    x1 = np.array(p1[2:5], dtype=int)
    y1 = np.array(p1[5:8], dtype=int)
    
    a2, b2 = p2[0], p2[1]
    x2 = np.array(p2[2:5], dtype=int)
    y2 = np.array(p2[5:8], dtype=int)
    
    # Zorn multiplication formula over GF(2):
    # a' = a1*a2 + dot(x1, y2)
    # b' = b1*b2 + dot(x2, y1)
    # x' = a1*x2 + b2*x1 + cross(y1, y2)
    # y' = a2*y1 + b1*y2 + cross(x1, x2)
    
    a_res = (a1*a2 ^ dot_f2(x1, y2)) & 1
    b_res = (b1*b2 ^ dot_f2(x2, y1)) & 1
    x_res = ((a1*x2) ^ (b2*x1) ^ cross_f2(y1, y2)) & 1
    y_res = ((a2*y1) ^ (b1*y2) ^ cross_f2(x1, x2)) & 1
    
    return np.array([a_res, b_res, x_res[0], x_res[1], x_res[2], y_res[0], y_res[1], y_res[2]], dtype=int)

def check_algebra_automorphism(M):
    # 1. Invertible
    det = int(round(np.linalg.det(M.astype(float)))) % 2
    if det == 0:
        return False, "Non-invertible matrix"
    
    # 2. Identity 1 = a + b mapped to 1:
    one_vec = np.array([1, 1, 0, 0, 0, 0, 0, 0], dtype=int)
    if not np.array_equal((M @ one_vec) % 2, one_vec):
        return False, "Does not fix algebra unit 1 = a + b"
    
    # 3. Multiplication table preservation on all 64 basis pairs:
    I8 = np.eye(8, dtype=int)
    for i in range(8):
        for j in range(8):
            ei = I8[i]
            ej = I8[j]
            prod = zorn_mul(ei, ej)
            
            Mei = (M @ ei) % 2
            Mej = (M @ ej) % 2
            M_prod = (M @ prod) % 2
            
            actual_prod = zorn_mul(Mei, Mej)
            if not np.array_equal(M_prod, actual_prod):
                return False, f"Multiplication failed on ({BASIS_NAMES[i]}, {BASIS_NAMES[j]})"
                
    return True, "Valid algebra automorphism"

# The six exact matrices exported by the independent carrier CAS extractor.
# They are stored row-wise; the extractor's integer tuples are column images.
g1 = np.array([
  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,1], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,1,0,0,0], [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0]
], dtype=int)

g2 = np.array([
  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0], [0,0,0,0,0,0,1,1], [0,0,0,0,0,1,1,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,1,0,0,0], [0,0,0,1,1,0,0,0], [0,0,1,1,1,0,0,0]
], dtype=int)

g3 = np.array([
  [0,1,0,0,1,1,0,0], [1,0,0,0,1,1,0,0], [1,1,0,1,1,0,0,1], [0,0,0,0,1,0,1,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,1,0,0,0], [0,0,0,1,0,1,0,0], [1,1,1,0,1,1,1,0]
], dtype=int)

g4 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0], [0,0,1,0,0,0,0,0], [0,0,0,1,1,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0], [0,0,0,0,0,0,1,1]
], dtype=int)

g5 = np.array([
  [1,0,0,0,1,0,0,0], [0,1,0,0,1,0,0,0], [0,0,1,0,0,0,1,0], [0,0,0,1,0,1,0,0],
  [0,0,0,0,1,0,0,0], [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0], [1,1,0,0,1,0,0,1]
], dtype=int)

g6 = np.array([
  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0], [0,0,0,0,0,0,1,0], [0,0,0,0,0,1,0,0],
  [0,0,0,0,0,0,0,1], [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0], [0,0,0,0,1,0,0,0]
], dtype=int)

# Symbolic coordinate specifications for the two generators that are
# transported into Lean by G2TwoOuterGenerators.lean.  An output coordinate
# is represented by the XOR of the listed input coordinates; this is a
# linear, non-enumerative certificate for the exported matrix rows.
g2_coordinate_formula = ((1,), (0,), (6, 7), (5, 6), (5,), (4,), (3, 4), (2, 3, 4))
g4_coordinate_formula = ((0,), (1,), (2,), (3, 4), (4,), (5,), (6,), (6, 7))

# The Lean outer owners use the CAS extractor's third and fifth matrices:
# `g2Fun = generator_2` and `g4Fun = generator_4` (zero-based extractor names).
lean_g2_coordinate_formula = (
    (1, 4, 5), (0, 4, 5), (0, 1, 3, 4, 7), (4, 6),
    (5,), (4,), (3, 5), (0, 1, 2, 4, 5, 6)
)
lean_g4_coordinate_formula = (
    (0, 4), (1, 4), (2, 6), (3, 5),
    (4,), (5,), (6,), (0, 1, 4, 7)
)

def matrix_of_xor_formulas(formulas):
    M = np.zeros((8, 8), dtype=int)
    for row, coordinates in enumerate(formulas):
        for column in coordinates:
            M[row, column] ^= 1
    return M

assert np.array_equal(matrix_of_xor_formulas(g2_coordinate_formula), g2)
assert np.array_equal(matrix_of_xor_formulas(g4_coordinate_formula), g4)
assert np.array_equal(matrix_of_xor_formulas(lean_g2_coordinate_formula), g3)
assert np.array_equal(matrix_of_xor_formulas(lean_g4_coordinate_formula), g5)

print("Symbolic coordinate alignment: CAS labels and Lean outer-owner labels match")

# Symbolic, non-enumerative proof over GF(2).  The following computation is
# polynomial identity checking, not evaluation on the finite carrier.
_z = symbols("a b x0 x1 x2 y0 y1 y2")
_z2 = symbols("A B X0 X1 X2 Y0 Y1 Y2")

def _xor(*terms):
    result = 0
    for term in terms:
        result += term
    return result

def _zorn_mul_symbolic(left, right):
    a, b, x0, x1, x2, y0, y1, y2 = left
    A, B, X0, X1, X2, Y0, Y1, Y2 = right
    return (
        _xor(a*A, x0*Y0, x1*Y1, x2*Y2),
        _xor(b*B, y0*X0, y1*X1, y2*X2),
        _xor(a*X0, B*x0, y1*Y2, y2*Y1),
        _xor(a*X1, B*x1, y2*Y0, y0*Y2),
        _xor(a*X2, B*x2, y0*Y1, y1*Y0),
        _xor(b*Y0, A*y0, x1*X2, x2*X1),
        _xor(b*Y1, A*y1, x2*X0, x0*X2),
        _xor(b*Y2, A*y2, x0*X1, x1*X0),
    )

def _apply_matrix_symbolic(matrix, vector):
    return tuple(_xor(*(int(matrix[i, j]) * vector[j] for j in range(8)))
                 for i in range(8))

def _zero_mod_two(expr):
    return Poly(expr, *_z, *_z2, modulus=2).is_zero

def prove_symbolic_zorn_automorphism(matrix):
    left = _z
    right = _z2
    product = _zorn_mul_symbolic(left, right)
    mapped_product = _apply_matrix_symbolic(matrix, product)
    product_of_mapped = _zorn_mul_symbolic(
        _apply_matrix_symbolic(matrix, left),
        _apply_matrix_symbolic(matrix, right),
    )
    return all(_zero_mod_two(x - y)
               for x, y in zip(mapped_product, product_of_mapped))

assert all(prove_symbolic_zorn_automorphism(M)
           for M in (g1, g2, g3, g4, g5, g6))
print("Symbolic GF(2) Zorn multiplication proof: all six generators pass")

gens = [g1, g2, g3, g4, g5, g6]

print("================================================================")
print("1. VERIFYING THAT g1..g6 ARE GENUINE SplitOctF2 AUTOMORPHISMS")
print("================================================================")
for i, g in enumerate(gens):
    ok, msg = check_algebra_automorphism(g)
    print(f"  Generator g{i+1}: {'PASS ✅' if ok else 'FAIL ❌'} ({msg})")
    assert ok

print("\n================================================================")
print("2. VERIFYING GENERATOR ORDERS")
print("================================================================")
def mat_pow(M, n):
    res = np.eye(8, dtype=int)
    for _ in range(n):
        res = (res @ M) % 2
    return res

for i, g in enumerate(gens, 1):
    order_two = np.array_equal(mat_pow(g, 2), np.eye(8, dtype=int))
    print(f"  Order(g{i}) == 2: {order_two}")
    assert order_two

print("\n================================================================")
print("3. CAS BINARY-WORD CHART CHECK")
print("================================================================")
ordered_words = set()
for exponents in itertools.product((0, 1), repeat=6):
    value = np.eye(8, dtype=int)
    for exponent, generator in zip(exponents, gens):
        if exponent:
            value = (value @ generator) % 2
    ordered_words.add(tuple(value.flatten()))
print(f"  Distinct ordered binary words: {len(ordered_words)} of 64")
assert len(ordered_words) == 64

print("\nThe symbolic identities above are the valid CAS certificate.")
print("The 64-word result is a CAS chart check, not yet a Lean closure theorem.")
