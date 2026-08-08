import sympy as sp

# Symbolically define Mellin-Shannon Sampling Theorem
# Reconstructing continuous thermodynamic potential from discrete prime-power samples

t, s, p = sp.symbols('t s p', real=True)
k = sp.Symbol('k', integer=True)

# Mellin transform representation
def mellin_transform(f, t, s):
    return sp.integrate(t**(s-1) * f, (t, 0, sp.oo))

# linc kernel (Mellin-sinc)
# linc(s) = sin(pi * ln(s)) / (pi * ln(s))
def linc(x):
    return sp.sin(sp.pi * sp.ln(x)) / (sp.pi * sp.ln(x))

# Reconstruction formula
F_s = sp.Function('F')(s)
sample_k = sp.Function('f')(p**k) # prime-power samples

print("Mellin-Shannon Interpolation:")
print("F(s) ~ sum( f(p^k) * linc(s / p^k) )")

interpolant = sp.Sum(sample_k * linc(s / p**k), (k, -sp.oo, sp.oo))
print("\nSymbolic Interpolant Formula:")
sp.pprint(interpolant)
