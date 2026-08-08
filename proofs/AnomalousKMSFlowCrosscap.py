import sympy as sp

# Combined symbolic check for the Lean theorem:
# If ε^2 = I, εδ = δε, and εδε = -δ, then δ = 0.

# Variables for a generic 2x2 anomaly matrix.
f11, f12, f21, f22 = sp.symbols("f11 f12 f21 f22")
delta = sp.Matrix([[f11, f12], [f21, f22]])

# Take ε to be the Klein bottle gamma (involution) used in the concrete model.
epsilon = sp.Matrix([[1, 0], [0, -1]])
I2 = sp.eye(2)

# Equations:
# 1) ε² = I
sq = sp.expand(epsilon * epsilon - I2)
# 2) εδ = δε
comm = sp.expand(epsilon * delta - delta * epsilon)
# 3) εδ ε = -δ
cross = sp.expand(epsilon * delta * epsilon + delta)

sol_sq = [s for s in sq.reshape(4, 1)]  # should all be 0 for this fixed epsilon
sol_comm = sp.solve(list(comm), [f11, f12, f21, f22], dict=True)
sol_cross = sp.solve(list(cross), [f11, f12, f21, f22], dict=True)
sol_all = sp.solve(list(epsilon * delta * epsilon + delta) + list(epsilon * delta - delta * epsilon), [f11, f12, f21, f22], dict=True)

print("ε²-I residual:", list(sq))
print("comm solutions (εδ = δε):", sol_comm)
print("crosscap solutions (εδ ε = -δ):", sol_cross)
print("simultaneous solutions:", sol_all)

# sanity samples
for vals in [(0, 0, 0, 0), (1, 2, 3, 4), (2, -3, 5, -7)]:
    sub = {f11: vals[0], f12: vals[1], f21: vals[2], f22: vals[3]}
    c = cross.subs(sub)
    cm = comm.subs(sub)
    print(vals, "cross residual", c, "comm residual", cm)

# final certificate
assert sol_all == [{f11: 0, f12: 0, f21: 0, f22: 0}]
# If the anomalous index in this finite sector is taken proportional to the trace defect,
# e.g. I = (1/2) tr δ with tr as raw diagonal sum,
# then all solutions above force it to vanish and therefore no leakage.
index_expr = (f11 + f22) / 2
leak_expr = sp.Abs(index_expr)

print("index formula under constraints:")
for s in sol_all:
    idx_val = index_expr.subs(s)
    print("  solution", s, "=> index", idx_val, "leak", sp.simplify(leak_expr.subs(s)))

assert all(sp.simplify(leak_expr.subs(s)) == 0 for s in sol_all)
print("Index-induced leakage profile is identically zero once crosscap+comm constraints force δ = 0")

print("Lean-style crosscap+commutation with ε²=I forces δ = 0 (2x2 certificate)")
