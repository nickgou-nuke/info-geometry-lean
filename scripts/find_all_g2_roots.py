import numpy as np

# Basis: e+ (0), e- (1), x0 (2), x1 (3), x2 (4), y0 (5), y1 (6), y2 (7)
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

def is_automorphism(M):
    one = np.array([1, 1, 0, 0, 0, 0, 0, 0], dtype=int)
    if not np.array_equal((M @ one) % 2, one):
        return False
    for i in range(8):
        ei = np.zeros(8, dtype=int); ei[i] = 1
        for j in range(8):
            ej = np.zeros(8, dtype=int); ej[j] = 1
            lhs = (M @ zorn_mul(ei, ej)) % 2
            rhs = zorn_mul((M @ ei) % 2, (M @ ej) % 2)
            if not np.array_equal(lhs, rhs):
                return False
    return True

# Weyl generators:
swap01 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,0,1]
], dtype=int)

cycle012 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,1,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,0,0,0,0,0,1],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0]
], dtype=int)

swapCartan = np.array([
  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,1], [0,0,1,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0]
], dtype=int)

c = (swapCartan @ cycle012) % 2 # Coxeter element of order 6
s = swap01                       # Simple reflection

# In G2 root system:
# 6 Short roots form a single orbit under c (and stable under s).
# 6 Long roots form a single orbit under c (and stable under s).

# Let's test short root candidates from the unipotent automorphisms:
u_short = np.eye(8, dtype=int); u_short[2, 3] = 1; u_short[6, 5] = 1

# Let's test long root candidate g4 from G2TwoOuterGenerators:
g4 = np.eye(8, dtype=int)
g4[0, 4] = 1
g4[1, 4] = 1
g4[2, 6] = 1
g4[3, 5] = 1
g4[7, 0] = g4[7, 1] = g4[7, 4] = 1

assert is_automorphism(u_short)
assert is_automorphism(g4)

# Generate short orbit:
short_orbit = []
for k in range(6):
    ck = np.linalg.matrix_power(c, k) % 2
    ck_inv = np.linalg.matrix_power(c, (6 - k) % 6) % 2
    short_orbit.append((ck @ u_short @ ck_inv) % 2)

# Generate long orbit:
long_orbit = []
for k in range(6):
    ck = np.linalg.matrix_power(c, k) % 2
    ck_inv = np.linalg.matrix_power(c, (6 - k) % 6) % 2
    long_orbit.append((ck @ g4 @ ck_inv) % 2)

print(f"Number of distinct short roots in orbit: {len({M.tobytes() for M in short_orbit})}")
print(f"Number of distinct long roots in orbit: {len({M.tobytes() for M in long_orbit})}")

# Check stability under s:
s_preserves_short = all(((s @ M @ s) % 2).tobytes() in {Sk.tobytes() for Sk in short_orbit} for M in short_orbit)
s_preserves_long = all(((s @ M @ s) % 2).tobytes() in {Lk.tobytes() for Lk in long_orbit} for M in long_orbit)

print(f"Does simple reflection s preserve the 6 short roots? {s_preserves_short}")
print(f"Does simple reflection s preserve the 6 long roots? {s_preserves_long}")


print("\n--- Detailed Root Permutation Table under W(G2) ---")
# Short roots S_0 .. S_5
# Long roots L_0 .. L_5

def find_root(M):
    for i, Sk in enumerate(short_orbit):
        if np.array_equal(M, Sk): return f"S_{i}"
    for i, Lk in enumerate(long_orbit):
        if np.array_equal(M, Lk): return f"L_{i}"
    return "UNKNOWN"

t = (s @ c) % 2
t_inv = t

print("Action of simple reflection s:")
for i, Sk in enumerate(short_orbit):
    print(f"  s(S_{i}) = {find_root((s @ Sk @ s) % 2)}")
for i, Lk in enumerate(long_orbit):
    print(f"  s(L_{i}) = {find_root((s @ Lk @ s) % 2)}")

print("\nAction of second simple reflection t:")
for i, Sk in enumerate(short_orbit):
    print(f"  t(S_{i}) = {find_root((t @ Sk @ t) % 2)}")
for i, Lk in enumerate(long_orbit):
    print(f"  t(L_{i}) = {find_root((t @ Lk @ t) % 2)}")


print("\n--- Steinberg Commutator Relations Table [x_r, x_s] ---")
def comm(A, B): return (A @ B @ A @ B) % 2

for i in range(6):
    for j in range(i+1, 6):
        res = comm(short_orbit[i], short_orbit[j])
        if not np.array_equal(res, np.eye(8, dtype=int)):
            print(f"  [S_{i}, S_{j}] = {find_root(res)}")

for i in range(6):
    for j in range(6):
        res = comm(short_orbit[i], long_orbit[j])
        if not np.array_equal(res, np.eye(8, dtype=int)):
            print(f"  [S_{i}, L_{j}] = {find_root(res)}")

for i in range(6):
    for j in range(i+1, 6):
        res = comm(long_orbit[i], long_orbit[j])
        if not np.array_equal(res, np.eye(8, dtype=int)):
            print(f"  [L_{i}, L_{j}] = {find_root(res)}")

