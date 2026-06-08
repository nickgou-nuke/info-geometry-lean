import sympy as sp
# Legendre duality: Φ(p) = sup_X(pX - f(X))
x, p = sp.symbols('x p')
f = x*sp.log(x) - x  # Boltzmann entropy
Phi = sp.exp(p)  # Legendre dual
Fisher = sp.diff(Phi, p, 2)
print(f"Fisher metric = {Fisher} = exp(p) = Φ''(p)")
