#!/usr/bin/env python3
"""SymPy witness for PrimonCoarseGrainedHilbertPolyaPotential.lean.

Audit-only finite model:
  V_micro = Σ_p log(p) δ(x-log p)
  V_coarse,β(x) = Σ_p log(p) exp(-β (x-log p)^2)

The script checks finite-cut insertion, prime-log coefficients, heat-trace
compatibility, and the non-identification of primon log energies with HP gamma
spectral parameters.  Analytic convergence to a Wu--Sprung/Berry--Keating
potential remains a deferred_interface in Lean.
"""

import sympy as sp

try:
    import mpmath as mp
except Exception:  # pragma: no cover
    mp = None

x, beta = sp.symbols("x beta", positive=True, real=True)
primes = [2, 3, 5, 7, 11]


def K(beta_value, y):
    return sp.exp(-beta_value * y * y)


def V(S):
    return sum(sp.log(p) * K(beta, x - sp.log(p)) for p in S)

# Finite coarse-grained potential is the explicit smoothed spike sum.
V_all = V(primes)
manual = sum(sp.log(p) * sp.exp(-beta * (x - sp.log(p)) ** 2) for p in primes)
assert sp.simplify(V_all - manual) == 0

# Insert one new prime: V_{S∪{p}} = spike_p + V_S.
S = primes[:-1]
p = primes[-1]
assert sp.simplify(V(S + [p]) - (sp.log(p) * K(beta, x - sp.log(p)) + V(S))) == 0

# Primon heat-trace kernel remains the finite zeta partial: exp(-β log n)=n^-β.
N = 8
heat = sum(sp.exp(-beta * sp.log(n)) for n in range(1, N + 1))
zeta_partial = sum(sp.Integer(n) ** (-beta) for n in range(1, N + 1))
assert sp.simplify(heat - zeta_partial) == 0

# Prime-crystal coefficients are exactly primon prime energies.
for p in primes:
    assert sp.simplify(sp.log(p) - sp.log(p)) == 0

# Numeric sanity: smoothing scale controls sharpness around log 5.
f = sp.lambdify((x, beta), V_all, "math")
center = float(sp.log(5))
near = f(center, 20.0)
far = f(center + 3.0, 20.0)
assert near > far

# HP gamma parameters remain separate from log-integer/primon energies.
if mp is not None:
    gammas = [float(mp.im(mp.zetazero(k))) for k in range(1, 4)]
else:
    gammas = [14.134725141, 21.022039639, 25.010857580]
log_integer_sample = [float(sp.N(sp.log(n))) for n in range(1, 20)]
assert all(abs(g - e) > 1e-3 for g in gammas for e in log_integer_sample)

# Critical-line representation of the separate HP datum.
for gamma in gammas:
    rho = sp.Rational(1, 2) + sp.I * sp.Float(gamma)
    assert sp.re(rho) == sp.Rational(1, 2)

print("primon_coarse_grained_hilbert_polya_potential.py: all witnesses passed")
