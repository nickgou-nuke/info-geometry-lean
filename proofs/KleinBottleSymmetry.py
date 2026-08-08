import sympy as sp

# 2x2 symbolic test of V₄ cross-cap forcing.
# ε is the chiral flip / parity involution.
f1, f2, g1, g2 = sp.symbols("f1 f2 g1 g2")

# Klein bottle chiral flip Γ = diag(1,-1).
epsilon = sp.Matrix([[1, 0], [0, -1]])
delta = sp.Matrix([[f1, f2], [g1, g2]])

# Conjugation by ε.
a = sp.simplify(epsilon * delta * epsilon)

# (1) Invariance equation: ε δ ε = δ
# (2) Cross-cap reversal: ε δ ε = -δ

eq_invar = sp.Matrix(a - delta)
eq_cross = sp.Matrix(a + delta)

# Solve each and their combination.
sol_invar = sp.solve(list(eq_invar), [f1, f2, g1, g2], dict=True)
sol_cross = sp.solve(list(eq_cross), [f1, f2, g1, g2], dict=True)
sol_both = sp.solve(list(eq_invar) + list(eq_cross), [f1, f2, g1, g2], dict=True)

print("εδϵ =", a)
print("invariance solutions:", sol_invar)
print("cross-cap solutions:", sol_cross)
print("simultaneous solutions:", sol_both)

# symbolic consistency identity: a = -a from the two hypotheses implies 2δ = 0
expr = sp.simplify(a + delta)
print("a + δ =", expr)

# numeric sanity check on samples
for vals in [(1, 2, 3, 4), (0, 0, 0, 0), (5, -3, 7, 11), (sp.Rational(1, 2), -7, 3, sp.Rational(-2, 3))]:
    v = {f1: vals[0], f2: vals[1], g1: vals[2], g2: vals[3]}
    inv_ok = (eq_invar.subs(v))
    cross_ok = (eq_cross.subs(v))
    print(vals, "inv residual =", inv_ok.T, "cross residual =", cross_ok.T)

# The symbolic elimination is the final algebraic certificate.
assert sol_both == [{f1: 0, f2: 0, g1: 0, g2: 0}]
print("KleinBottleSymmetry.py: εδϵ = δ and εδϵ = -δ force δ = 0")
