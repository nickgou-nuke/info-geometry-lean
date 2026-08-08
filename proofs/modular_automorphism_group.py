"""SymPy witness: finite-dimensional modular automorphism group.

For a faithful density matrix rho, the Tomita--Takesaki modular flow is
    sigma_t(A) = rho^(i t) A rho^(-i t)
Equivalently, with modular Hamiltonian K=-log rho,
    sigma_t(A)=exp(-i t K) A exp(i t K).
For diagonal rho=diag(p,q), off-diagonal matrix units acquire phases
    E12 -> (p/q)^(i t) E12,  E21 -> (q/p)^(i t) E21.
"""

import sympy as sp

print("§1  finite-dimensional modular flow")
p, q, t, s = sp.symbols("p q t s", positive=True, real=True)
I = sp.I
E12 = sp.Matrix([[0, 1], [0, 0]])
E21 = sp.Matrix([[0, 0], [1, 0]])

def D(x):
    return sp.diag(p**(I*x), q**(I*x))

def sigma(x, A):
    return sp.simplify(D(x) * A * D(-x))

assert sigma(0, E12) == E12
assert sigma(0, E21) == E21
assert sp.simplify(sigma(t, E12)[0, 1] / (p**(I*t)*q**(-I*t)) - 1) == 0
assert sp.simplify(sigma(t, E21)[1, 0] / (p**(-I*t)*q**(I*t)) - 1) == 0
print("   sigma_0=id and off-diagonal modular phases verified ✓")

print("§2  group law on matrix units")
left = sigma(t, sigma(s, E12))
right = sigma(t+s, E12)
assert sp.simplify(left[0,1] / right[0,1] - 1) == 0
left = sigma(t, sigma(s, E21))
right = sigma(t+s, E21)
assert sp.simplify(left[1,0] / right[1,0] - 1) == 0
print("   sigma_t ∘ sigma_s = sigma_{t+s} on generators ✓")

print("§3  KMS imaginary-time scaling")
beta = sp.symbols("beta", positive=True, real=True)
# At imaginary time i beta, E12 scales by p^{-beta} q^{beta}=(q/p)^beta.
scale_imag = sp.simplify(p**(I*(I*beta)) * q**(-I*(I*beta)))
assert sp.simplify(scale_imag / (p**(-beta) * q**beta) - 1) == 0
print("   imaginary modular time produces thermal Boltzmann ratio ✓")

print()
print("modular_automorphism_group.py: All identities verified")
