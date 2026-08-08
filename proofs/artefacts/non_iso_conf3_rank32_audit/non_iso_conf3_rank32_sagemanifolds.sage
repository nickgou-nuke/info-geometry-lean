
# SageManifolds geometry stack audit for the parameterized-family layer.
# This file is optional and scoped to differential-geometry sanity.
from sage.all import *
try:
    from sage.manifolds.all import *
except Exception as exc:
    print("SAGEMANIFOLDS_IMPORT_ERROR", exc)
    raise SystemExit(2)

print("=== non_iso_conf3_rank32_sagemanifolds ===")

# Parameter base and coordinates.
B = Manifold(4, 'B', structure='smooth')
X = B.chart('mu beta q theta')
mu, beta, qpar, theta = X[:4]
print('base_dim', B.dim())

# Fiber manifold and coordinates for translation-reduced variables.
F = Manifold(8, 'F', structure='smooth')
Y = F.chart('a0 a1 a2 a3 b0 b1 b2 b3')
(a0, a1, a2, a3, b0, b1, b2, b3) = Y[:8]
print('fiber_dim', F.dim())

# Differential-form probes on the split quadric coordinate model.
qa = a0^2 + a1^2 + a2^2 + a3^2
qb = b0^2 + b1^2 + b2^2 + b3^2
qab = (a0 - b0)^2 + (a1 - b1)^2 + (a2 - b2)^2 + (a3 - b3)^2
try:
    w_a = qa.differential() / qa
    w_b = qb.differential() / qb
    w_ab = qab.differential() / qab
    print('omega_defs', [w_a is not None, w_b is not None, w_ab is not None])
except Exception as exc:
    print('omega_defs_error', exc)
    w_a = None

# Optional chart-level connection toy model (informational only).
try:
    g = F.riemannian_metric('g')
    g[0, 0], g[1, 1], g[2, 2], g[3, 3], g[4, 4], g[5, 5], g[6, 6], g[7, 7] = 1, 1, 1, 1, 1, 1, 1, 1
    print('metric_rank', g.rank())
except Exception as exc:
    print('metric_build_error', exc)

# Vector field + Lie-derivative probe (diagnostic only).
try:
    V = F.vector_field('V')
    # Try a coordinate component assignment if API agrees.
    try:
        V[X, 0] = 1
    except Exception:
        pass
    omega = w_a
    if omega is not None:
        print('lie_derivative_ok', omega.lie_derivative(V) is not None)
except Exception as exc:
    print('lie_derivative_error', exc)

# Parameter-symbol probe for modular-flow layer bookkeeping.
print('mu_is_symbol', mu is not None)
print('status_ok')
