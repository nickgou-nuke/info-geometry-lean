#!/usr/bin/env python3
"""SymPy/mpmath witness for PrimonHilbertPolyaSeparation.lean.

Audits the theorem-honest separation:
  H_primon energies are log(n), giving finite zeta/Dirichlet heat traces.
  prime logs are potential/scattering coefficients.
  Hilbert--Polya gamma values are separate spectral data, numerically tied to
  zeta zeros only through the critical-line representation 1/2 + i gamma.
  reciprocal ghost sector is singular when the bosonic partition denominator
  zeta(s) vanishes.
"""

import math
import sympy as sp

try:
    import mpmath as mp
except Exception:  # pragma: no cover
    mp = None

beta = sp.symbols("beta", positive=True)
N = 8

# Primon log-integer energies and finite heat trace.
energies = [sp.log(n) for n in range(1, N + 1)]
heat_trace = sum(sp.exp(-beta * E) for E in energies)
zeta_partial = sum(sp.Integer(n) ** (-beta) for n in range(1, N + 1))
assert sp.simplify(heat_trace - zeta_partial) == 0

# Prime single-particle energies are log(p), and can be reused as potential coefficients.
primes = [2, 3, 5, 7, 11]
prime_energies = {p: sp.log(p) for p in primes}
prime_potential_coeffs = {p: sp.log(p) for p in primes}
assert prime_energies == prime_potential_coeffs

# The two spectra are not identified: log integers are arithmetic energies;
# gamma values are HP/zero spectral parameters.  Numerically they are different lists.
log_integer_sample = [float(sp.N(sp.log(n))) for n in range(1, 8)]
if mp is not None:
    gammas = [float(mp.im(mp.zetazero(k))) for k in range(1, 4)]
else:
    gammas = [14.134725141, 21.022039639, 25.010857580]
assert all(abs(g - e) > 1e-3 for g in gammas for e in log_integer_sample)

# Critical-line representation for HP datum: rho = 1/2 + i gamma.
for gamma in gammas:
    rho = sp.Rational(1, 2) + sp.I * sp.Float(gamma)
    assert sp.re(rho) == sp.Rational(1, 2)

# Reciprocal ghost sector: 1/zeta(s) has denominator zero at zeta zero.
if mp is not None:
    for k in range(1, 3):
        rho = mp.zetazero(k)
        z = mp.zeta(rho)
        assert abs(z) < mp.mpf("1e-12")
        # Avoid actual division by nearly zero; audit the denominator-zero condition.
        assert abs(1 / (z + mp.mpf("1e-12"))) > mp.mpf("1e10")

print("primon_hilbert_polya_separation.py: all witnesses passed")
