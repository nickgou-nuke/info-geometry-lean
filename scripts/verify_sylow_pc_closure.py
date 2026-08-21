import numpy as np

# Exact Sylow 2-subgroup polycyclic generators from GAP:
s1 = np.array([
    [1, 0, 0, 1, 0, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 1]
], dtype=int)

s2 = np.array([
    [1, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0, 0],
    [1, 1, 0, 1, 1, 0, 0, 1],
    [0, 0, 1, 1, 0, 1, 1, 1],
    [0, 0, 1, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 1]
], dtype=int)

s3 = np.array([
    [1, 0, 1, 0, 0, 0, 0, 1],
    [0, 1, 1, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 1],
    [0, 0, 1, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 1]
], dtype=int)

s4 = np.array([
    [1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 1]
], dtype=int)

s5 = np.array([
    [1, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [1, 1, 0, 1, 1, 0, 0, 1],
    [0, 0, 0, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 1]
], dtype=int)

s6 = np.array([
    [1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1]
], dtype=int)

s_gens = [s1, s2, s3, s4, s5, s6]

# Zorn multiplication definition:
def zorn_mul(u, v):
    a1, b1 = u[0], u[1]
    x1, y1 = u[2:5], u[5:8]
    a2, b2 = v[0], v[1]
    x2, y2 = v[2:5], v[5:8]
    
    a3 = (a1 * a2 + np.dot(x1, y2)) % 2
    b3 = (b1 * b2 + np.dot(y1, x2)) % 2
    x3 = (a1 * x2 + b2 * x1 - np.cross(y1, y2)) % 2
    y3 = (b1 * y2 + a2 * y1 + np.cross(x1, x2)) % 2
    return np.concatenate([[a3, b3], x3, y3]).astype(int)

# 1. Verify that all 6 matrices are genuine automorphisms:
for k, M in enumerate(s_gens):
    # Check unit preservation:
    one = np.array([1, 1, 0, 0, 0, 0, 0, 0], dtype=int)
    assert np.array_equal((M @ one) % 2, one), f"s{k+1} fails unit preservation"
    
    # Check all 64 basis pairs:
    for i in range(8):
        ei = np.zeros(8, dtype=int)
        ei[i] = 1
        for j in range(8):
            ej = np.zeros(8, dtype=int)
            ej[j] = 1
            eij = zorn_mul(ei, ej)
            lhs = (M @ eij) % 2
            rhs = zorn_mul((M @ ei) % 2, (M @ ej) % 2)
            assert np.array_equal(lhs, rhs), f"s{k+1} fails multiplication preservation on basis ({i}, {j})"
    print(f"Sylow generator s{k+1}: PASS ✅ (Valid algebra automorphism)")

# 2. Evaluate all 64 ordered polycyclic words:
words_dict = {}
words_list = []

for e1 in range(2):
    for e2 in range(2):
        for e3 in range(2):
            for e4 in range(2):
                for e5 in range(2):
                    for e6 in range(2):
                        tup = (e1, e2, e3, e4, e5, e6)
                        M = np.eye(8, dtype=int)
                        for k, e in enumerate(tup):
                            if e == 1:
                                M = (M @ s_gens[k]) % 2
                        M_bytes = M.tobytes()
                        words_dict[M_bytes] = tup
                        words_list.append((M, tup))

print(f"\nTotal distinct words: {len(words_dict)} / 64")
assert len(words_dict) == 64

# 3. Verify that the 64 words form a strictly closed group:
is_closed = True
for M1, tup1 in words_list:
    for M2, tup2 in words_list:
        prod = (M1 @ M2) % 2
        if prod.tobytes() not in words_dict:
            is_closed = False
            break

print(f"Is the 64-element set STRICTLY CLOSED under multiplication? {is_closed} ✅")
assert is_closed

print("\n🏆 CAS PROOF COMPLETE: Sylow 2-subgroup B <= SplitOctF2Aut of size EXACTLY 64 is 100% proved in CAS!")
