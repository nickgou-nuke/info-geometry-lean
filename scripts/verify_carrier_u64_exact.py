#!/usr/bin/env python3
"""
CARRIER-LEVEL EXACT VERIFICATION FOR G2(2) BOREL SUBGROUP OF ORDER 64
ON THE SPLIT OCTONION ALGEBRA OVER GF(2)
"""

import itertools
import numpy as np

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

# The 6 exact matrices from GAP:
g1 = np.array([
  [ 0, 1, 0, 0, 0, 1, 0, 0 ], [ 1, 0, 0, 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 1, 0, 0, 0, 1 ], [ 0, 0, 0, 0, 1, 1, 1, 0 ], 
  [ 0, 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 0, 0, 1, 0, 0, 0 ], 
  [ 0, 0, 0, 1, 0, 0, 0, 0 ], [ 1, 1, 1, 1, 0, 1, 0, 0 ]
], dtype=int)

g2 = np.array([
  [ 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0, 0, 0, 0 ], 
  [ 0, 0, 1, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 1, 1, 0, 0, 0 ], 
  [ 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 1, 1 ]
], dtype=int)

g3 = np.array([
  [ 1, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 1, 0, 0, 1, 0, 0, 0 ], 
  [ 0, 0, 1, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 1, 1, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 0, 0, 1, 0 ], [ 1, 1, 0, 0, 1, 0, 1, 1 ]
], dtype=int)

g4 = np.array([
  [ 1, 0, 0, 0, 1, 1, 0, 0 ], [ 0, 1, 0, 0, 1, 1, 0, 0 ], 
  [ 1, 1, 1, 1, 1, 0, 1, 0 ], [ 0, 0, 0, 1, 1, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 1, 1, 1, 0 ], [ 1, 1, 0, 1, 0, 1, 1, 1 ]
], dtype=int)

g5 = np.array([
  [ 1, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 1, 0, 0, 1, 0, 0, 0 ], 
  [ 0, 0, 1, 1, 0, 1, 1, 0 ], [ 0, 0, 0, 1, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 0, 1, 1, 0 ], [ 1, 1, 0, 0, 1, 0, 0, 1 ]
], dtype=int)

g6 = np.array([
  [ 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0, 0, 0, 0 ], 
  [ 0, 0, 1, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 1, 0, 0, 0, 0 ], 
  [ 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0 ], 
  [ 0, 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 1 ]
], dtype=int)

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

print(f"  Order(g1) == 4: {np.array_equal(mat_pow(g1, 4), np.eye(8, dtype=int)) and not np.array_equal(mat_pow(g1, 2), np.eye(8, dtype=int))}")
for i in range(1, 6):
    print(f"  Order(g{i+1}) == 2: {np.array_equal(mat_pow(gens[i], 2), np.eye(8, dtype=int))}")

print("\n================================================================")
print("3. VERIFYING 64-WORD ORDERED PRODUCT INJECTIVITY")
print("================================================================")
prods = {}
for e in itertools.product([0, 1], repeat=6):
    res = np.eye(8, dtype=int)
    for i in range(6):
        if e[i]:
            res = (res @ gens[i]) % 2
    prods[e] = tuple(res.flatten())

num_distinct = len(set(prods.values()))
print(f"  Distinct ordered products g1^e1 ... g6^e6: {num_distinct} of 64")
assert num_distinct == 64

print("\n================================================================")
print("4. VERIFYING SUBGROUP CLOSURE (IS THE SET OF 64 CLOSED?)")
print("================================================================")
prod_set = set(prods.values())
closed = True
for m1_t in prod_set:
    M1 = np.array(m1_t, dtype=int).reshape((8, 8))
    for m2_t in prod_set:
        M2 = np.array(m2_t, dtype=int).reshape((8, 8))
        M12 = (M1 @ M2) % 2
        if tuple(M12.flatten()) not in prod_set:
            closed = False
            break
    if not closed:
        break

print(f"  Is the 64-element set closed under multiplication? {closed} {'✅' if closed else '❌'}")
assert closed

print("\n🏆 COMPLETE CARRIER-LEVEL SUCCESS:")
print("   - All 6 matrices are kernel-true SplitOctF2 automorphisms.")
print("   - The 64 ordered products are 100% injective.")
print("   - The 64 elements form a closed Sylow 2-subgroup B <= SplitOctF2Aut!")
