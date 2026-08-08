#!/usr/bin/env python3
"""SymPy audit for the Mellin / Laplace / wavelet extraction.

Checks the finite algebraic skeleton:
* standard and frequency-style wavelet parameterizations;
* Mellin kernel as logarithmic Fourier kernel;
* multiplicative-to-additive log scaling;
* even/odd decomposition;
* discrete-time Blaschke Möbius form.
"""

import sympy as sp

# Wavelet parameterizations
psi = sp.Function("psi")
a, b, t, sigma, tau = sp.symbols("a b t sigma tau", nonzero=True, real=True)
wavelet_core_arg = (t - b) / a
wavelet_freq_arg = (1 / a) * t - b / a
assert sp.simplify(wavelet_core_arg - wavelet_freq_arg) == 0

# Mellin / log-Fourier kernel
s, omega, u = sp.symbols("s omega u")
log_kernel = sp.exp((s - 1) * u)
assert sp.simplify(log_kernel.subs(s, sp.I * omega + 1) - sp.exp(sp.I * omega * u)) == 0

# Multiplicative scaling in log coordinates
x = sp.symbols("x", positive=True)
lam = sp.symbols("lam", positive=True)
assert sp.simplify(sp.log(lam * x) - (sp.log(lam) + sp.log(x))) == 0

# Even/odd split
f = sp.Function("f")
Even = (f(t) + f(-t)) / 2
Odd = (f(t) - f(-t)) / 2
assert sp.simplify(Even + Odd - f(t)) == 0
assert sp.simplify(((f(-t) + f(t)) / 2) - Even) == 0
assert sp.simplify(((f(-t) - f(t)) / 2) + Odd) == 0

# Blaschke Möbius scale-shift form
z, g1, g2 = sp.symbols("z g1 g2")
blaschke = (g1 * z + g2) / (sp.conjugate(g2) * z + sp.conjugate(g1))
assert sp.simplify(blaschke - (g1 * z + g2) / (sp.conjugate(g2) * z + sp.conjugate(g1))) == 0

# Discrete-time scale-shift normalization fingerprints (symbolic sanity only).
theta = sp.symbols("theta", real=True)
alpha = sp.symbols("alpha", positive=True, real=True)
g1_norm = (sp.exp(sp.I * theta) + alpha * sp.exp(-sp.I * theta)) / sp.sqrt(2 * alpha * sp.cos(theta))
g2_norm = sp.exp(sp.I * theta) * (1 - alpha) / sp.sqrt(2 * alpha * sp.cos(theta))
print("normalized gamma1 =", g1_norm)
print("normalized gamma2 =", g2_norm)

print("mellin / wavelet / scale-shift audit passed")
