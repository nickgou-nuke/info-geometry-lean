import numpy as np

s = [1, 1, 1, -1, 1, 1, 1]
lines = [
    (0, 1, 2),
    (0, 3, 4),
    (0, 5, 6),
    (1, 3, 5),
    (1, 4, 6),
    (2, 3, 6),
    (2, 4, 5)
]

def cross(u, v):
    res = np.zeros(7)
    for idx, (a, b, c) in enumerate(lines):
        si = s[idx]
        res[c] += si * (u[a] * v[b] - u[b] * v[a])
        res[a] += si * (u[b] * v[c] - u[c] * v[b])
        res[b] += si * (u[c] * v[a] - u[a] * v[c])
    return res

def dot7(u, v):
    return np.dot(u, v)

# Test 10 random pairs u, v
np.random.seed(42)
for _ in range(10):
    u = np.random.randn(7)
    v = np.random.randn(7)
    lhs = dot7(cross(u, v), cross(u, v))
    rhs = dot7(u, u) * dot7(v, v) - dot7(u, v)**2
    print("LHS:", lhs)
    print("RHS:", rhs)
    print("Diff:", lhs - rhs)
