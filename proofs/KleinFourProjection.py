import math
import sympy as sp

# ==========================================================
# Klein four-group action on the 4D Klein-bottle embedding coordinates
# ==========================================================

# Parameters of the 4D immersion
R = 3.0
r = 1.0


def klein4(u: float, v: float, R: float = R, r: float = r):
    """4D Klein-type immersion with (u,v) coordinates.

    X = (R + r cos v) cos u
    Y = (R + r cos v) sin u
    Z = r sin v cos(u/2)
    W = r sin v sin(u/2)
    """
    return sp.Matrix([
        (R + r * math.cos(v)) * math.cos(u),
        (R + r * math.cos(v)) * math.sin(u),
        r * math.sin(v) * math.cos(u / 2),
        r * math.sin(v) * math.sin(u / 2),
    ])


# V4 generators as commuting involutions (180-degree flips in orthogonal planes).
# A: flips the (Z,W) block  -> deck shift of u by 2π on this immersion.
A = sp.diag(1, 1, -1, -1)
# B: flips the (X,Y) block -> second independent involution.
B = sp.diag(-1, -1, 1, 1)
I4 = sp.eye(4)

# Group law checks
assert A * A == I4
assert B * B == I4
assert A * B == B * A
assert A * B * A * B == I4

# C = AB
C = A * B


def proj3_orth(x4: sp.Matrix):
    """Orthographic shadow of 4D coordinates into R^3."""
    return sp.Matrix(x4[:3])


def proj3_persp(x4: sp.Matrix, alpha: float = 4.0):
    """Perspective projection to R^3 using W as depth-like coordinate."""
    x, y, z, w = map(float, x4)
    return sp.Matrix([x / (alpha + w), y / (alpha + w), z / (alpha + w)])


# Sample grid points on the 4D Klein-like immersion
samples = [
    (0.2, 0.4),
    (1.0, 1.1),
    (2.5, -0.9),
    (4.2, 0.2),
]

print("===== V4 Klein action on sample points =====")
for u, v in samples:
    p = klein4(u, v)
    pA = A * p
    pB = B * p
    pC = C * p
    print("(u,v)=", (u, v))
    print(" p  :", [round(float(x), 6) for x in p])
    print(" A p:", [round(float(x), 6) for x in pA], "(A = (u,v) + 2π shift)")
    print(" B p:", [round(float(x), 6) for x in pB], "(orthogonal 180° flip in XY)")
    print(" C p:", [round(float(x), 6) for x in pC])
    print(" orth proj    p, A p, B p, C p:")
    print("  ", [round(float(x), 6) for x in proj3_orth(p)])
    print("  ", [round(float(x), 6) for x in proj3_orth(pA)])
    print("  ", [round(float(x), 6) for x in proj3_orth(pB)])
    print("  ", [round(float(x), 6) for x in proj3_orth(pC)])
    print(" persp proj p, A p:", [round(float(x), 6) for x in proj3_persp(p)],
          [round(float(x), 6) for x in proj3_persp(pA)])
    print("----")

print("===== Algebraic checks =====")
print("A*B=B*A:", (A * B - B * A) == sp.zeros(4))
print("det(A), det(B):", float(A.det()), float(B.det()))


# ==========================================================
# 3D shadow diagnostics: where the projection folds (pinch mechanism)
# ==========================================================


def shadow_norm(p: sp.Matrix, q: sp.Matrix) -> float:
    """Euclidean 3D distance between orthographic shadows of two 4D points."""
    d = proj3_orth(p) - proj3_orth(q)
    return float(sp.sqrt((d[0] ** 2 + d[1] ** 2 + d[2] ** 2)))


print("===== 3D shadow pinch diagnostics =====")
# Compare points that should be V4-related by u -> u + 2π (sheet exchange)
for u in [0.0, 0.8, 1.6, 2.4, 3.2, 4.0, 5.0]:
    closest = None
    for v in [ -1.6, -1.0, -0.5, -0.2, -0.1, -0.05, -0.02, -0.01,
               0.0, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 1.6]:
        p = klein4(u, v)
        p_shift = klein4(u + 2 * math.pi, v)
        d_shadow = shadow_norm(p, p_shift)
        if closest is None or d_shadow < closest[0]:
            closest = (d_shadow, float(v), float(p[2]), float(p[3]))
    if closest is not None:
        d_shadow, v_star, z_star, w_star = closest
        print(
            "u=", round(u, 2),
            " minimal shadow distance=", round(d_shadow, 8),
            " at v=", round(v_star, 3),
            " (z,w)=", (round(z_star, 6), round(w_star, 6)),
            ", pinch carrier when z,w→0"
        )

# Export a compact sampled shadow list (for downstream plotting in your renderer).
# First 20 sample rows: u, v, X, Y, Z, W, x3, y3, z3
print("===== Export: shadow sample seed rows =====")
for i, (u, v) in enumerate(
    [(2 * math.pi * i / 12, -math.pi + 2 * math.pi * j / 12)
     for i in range(7) for j in range(7)]
):
    p = klein4(u, v)
    s = proj3_orth(p)
    print(f"row {i:02d}: {u:.4f} {v:.4f} "
          f"{float(p[0]): .6f} {float(p[1]): .6f} {float(p[2]): .6f} {float(p[3]): .6f} "
          f"{float(s[0]): .6f} {float(s[1]): .6f} {float(s[2]): .6f}")

