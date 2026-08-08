import random
import sympy as sp

# Coordinate symmetry and convexity probes for the critical-axis model.
# This file is a symbolic/numeric companion to ZetaCoordinateSymmetry.lean.

sigma, t, mu = sp.symbols("sigma t mu", real=True)
V = -sp.log(sigma) - sp.log(1 - sigma) + (t ** 2 + mu ** 2)

# 1) Exact involutive symmetry: V(1-sigma, t, mu) = V(sigma, t, mu)
_symm = sp.simplify(V.subs(sigma, 1 - sigma) - V)
assert sp.simplify(_symm) == 0

# 2) Hessian diagonal entries (closed form).
V_s = sp.diff(V, sigma)
V_ss = sp.simplify(sp.diff(V_s, sigma))
V_tt = sp.simplify(sp.diff(V, t, 2))
V_mumu = sp.simplify(sp.diff(V, mu, 2))
print("∂²V/∂σ² =", V_ss)
print("∂²V/∂t² =", V_tt)
print("∂²V/∂mu² =", V_mumu)

# 3) Axis-value strict minimum in sampled section (fixing t,mu) from symmetry + convexity numerics.
def axis_lock_samples(sample_points):
    for s0, t0, m0 in sample_points:
        axis = float(sp.N(V.subs({sigma: sp.Rational(1, 2), t: t0, mu: m0})))
        for s in [0.05, 0.2, 0.4, 0.6, 0.8, 0.95]:
            if s == 0.5:
                continue
            v = float(sp.N(V.subs({sigma: sp.Rational(s), t: t0, mu: m0})))
            assert axis < v, f"axis lock violated at s={s}, params={(t0,m0)}"

axis_lock_samples([(0.3, 0.7, -0.2), (1.4, -0.5, 0.4), (0.0, 2.0, 1.0)])

# 4) Numeric directional self-concordance check on a random finite sample.
# For direction h = (h_sigma, h_t, h_mu), only h_sigma contributes to D^3 V
# because V is quadratic in t and mu.
V_sss = sp.simplify(sp.diff(V_ss, sigma))


def directional_terms(sval, ht, hm, hs):
    hsq = hs ** 2
    h3 = (hs ** 3) * float(V_sss.subs(sigma, sval))
    h2 = (hsq) * float(V_ss.subs(sigma, sval))
    return abs(h3), h2

for _ in range(50):
    s_val = 0.02 + 0.96 * random.random()
    hs = -2.0 + 4.0 * random.random()
    ht = -1.0 + 2.0 * random.random()
    hm = -1.0 + 2.0 * random.random()
    lhs, rhs_quad = directional_terms(s_val, ht, hm, hs)
    rhs = 2.0 * (rhs_quad ** 1.5)
    assert lhs <= rhs + 1e-10, "numerical self-concordance check failed"

print("ZetaCoordinateSymmetry.py: symmetry, axis-lock samples, and directional self-concordance checks passed")
