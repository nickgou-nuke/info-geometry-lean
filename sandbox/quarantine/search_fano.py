import itertools
import numpy as np

lines = [
    (0, 1, 2),
    (0, 3, 4),
    (0, 5, 6),
    (1, 3, 5),
    (1, 4, 6),
    (2, 3, 6),
    (2, 4, 5)
]

def get_fano_cross(s):
    def cross(u, v):
        res = np.zeros(7)
        for idx, (a, b, c) in enumerate(lines):
            si = s[idx]
            res[c] += si * (u[a] * v[b] - u[b] * v[a])
            res[a] += si * (u[b] * v[c] - u[c] * v[b])
            res[b] += si * (u[c] * v[a] - u[a] * v[c])
        return res
    return cross

def test_signs(s):
    cross = get_fano_cross(s)
    def pmul(x, y):
        x_s, x_v = x[0], x[1]
        y_s, y_v = y[0], y[1]
        return (
            x_s * y_s - np.dot(x_v, y_v),
            x_s * y_v + y_s * x_v + cross(x_v, y_v)
        )
        
    np.random.seed(42)
    for _ in range(50):
        x = (np.random.randn(), np.random.randn(7))
        y = (np.random.randn(), np.random.randn(7))
        # Left alt: (x * x) * y = x * (x * y)
        lhs_l = pmul(pmul(x, x), y)
        rhs_l = pmul(x, pmul(x, y))
        # Right alt: (x * y) * y = x * (y * y)
        lhs_r = pmul(pmul(x, y), y)
        rhs_r = pmul(x, pmul(y, y))
        if np.linalg.norm(lhs_l[0] - rhs_l[0]) > 1e-10 or np.linalg.norm(lhs_l[1] - rhs_l[1]) > 1e-10:
            return False
        if np.linalg.norm(lhs_r[0] - rhs_r[0]) > 1e-10 or np.linalg.norm(lhs_r[1] - rhs_r[1]) > 1e-10:
            return False
    return True

valid = []
for s in itertools.product([-1, 1], repeat=7):
    if test_signs(s):
        valid.append(s)

print(f"Total valid: {len(valid)}")
for v in valid:
    print(v)
