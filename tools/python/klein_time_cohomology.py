import sympy as sp

# Coordinates
t, x, y, z = sp.symbols('t x y z', real=True)

# Differentials
dt, dx, dy, dz = sp.symbols('dt dx dy dz')

# Pauli basis representation of a point in Minkowski space (the causal algebra)
Q = sp.Matrix([
    [t + z, x - sp.I * y],
    [x + sp.I * y, t - z]
])

# Determinant of Q gives the Klein quadric (Minkowski metric)
det_Q = Q.det()
print(f"Determinant of Q (The Klein Quadric): {sp.simplify(det_Q)}")

# Differential of Q
dQ = sp.Matrix([
    [dt + dz, dx - sp.I * dy],
    [dx + sp.I * dy, dt - dz]
])

# Inverse of Q
Q_inv = Q.inv()

# The 1-form d(log Q) = dQ * Q^-1
dlogQ = dQ * Q_inv

# The trace of dlogQ is exactly d(log(det Q))
tr_dlogQ = sp.simplify(sp.trace(dlogQ))
print(f"\nTrace of d(log Q) (The de Rham 1-form):")
print(sp.pretty(sp.simplify(tr_dlogQ)))

# Show that it's d(det_Q) / det_Q
d_det_Q = sp.diff(det_Q, t)*dt + sp.diff(det_Q, x)*dx + sp.diff(det_Q, y)*dy + sp.diff(det_Q, z)*dz
d_det_Q_over_det_Q = sp.simplify(d_det_Q / det_Q)

print(f"\nd(det Q) / det Q:")
print(sp.pretty(d_det_Q_over_det_Q))

print(f"\nEquality verified: {sp.simplify(tr_dlogQ - d_det_Q_over_det_Q) == 0}")

