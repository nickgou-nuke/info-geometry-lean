import sympy as sp

# Connes--Chamseddine-style quadratic spectral profile in the finite 2x2 sector.
# We model the anomaly argument by the trace anomaly scalar t = tr(δK),
a, b, c, d, S0, cpl = sp.symbols("a b c d S0 cpl", real=True)

delta = sp.Matrix([[a, b], [c, d]])

def tr(mat):
    return mat.trace()

# Fixed Klein involution used in the concrete sector.
epsilon = sp.Matrix([[1, 0], [0, -1]])

# Cross-cap and symmetry constraints used by the anomaly trap.
h_cross = sp.expand(epsilon * delta * epsilon + delta)      # εδ ε + δ = 0
h_comm = sp.expand(epsilon * delta - delta * epsilon)       # εδ - δε = 0

# Solve the exact algebraic constraints.
sol_cross = sp.solve(list(h_cross), [a, b, c, d], dict=True)
sol_comm = sp.solve(list(h_comm), [a, b, c, d], dict=True)
sol_both = sp.solve(list(h_cross) + list(h_comm), [a, b, c, d], dict=True)

print("cross-cap constraints:", sol_cross)
print("comm constraints:", sol_comm)
print("simultaneous constraints:", sol_both)

# Spectral action profile S(δ) = S0 + cpl * |tr(δ)|^2
S = S0 + cpl * (sp.expand(tr(delta) ** 2))

# Under exact constraints δ=0, hence tr(δ)=0 and action reduces to S0.
for s in sol_both:
    sv = {k: sp.simplify(v) for k, v in s.items()}
    print("solution", sv, "=> tr(δ)=", tr(delta).subs(sv), "=> S=", S.subs(sv))

# Formal check: if cpl > 0 and both constraints hold, only one solution, so minimum is S0.
assert sol_both == [{a: 0, b: 0, c: 0, d: 0}]

# Numerical spot-check (real values) of nonzero candidates:
sample = [
    (0, 0, 0, 0),
    (2, 1, -1, 3),
    (1, -2, 5, -4),
]
for vals in sample:
    sdict = {a: vals[0], b: vals[1], c: vals[2], d: vals[3], cpl: 7.0, S0: 1.5}
    sδ = float(S.subs(sdict).evalf())
    resid_trace = float((tr(delta) ** 2).subs(sdict))
    print("vals", vals, "tr(δ)^2", resid_trace, "S", sδ)
    if vals != (0, 0, 0, 0):
        print("  offset above baseline:", sδ - 1.5)

print("ConnesSpectralAction sanity: with crosscap+commutation, only δ=0, so S is minimized at S0.")
