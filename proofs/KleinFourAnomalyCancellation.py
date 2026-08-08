import sympy as sp

# V4 group elements as pairs in Z2 x Z2.
V4 = [(0, 0), (1, 0), (0, 1), (1, 1)]

def v4_mul(a, b):
    return ((a[0] + b[0]) % 2, (a[1] + b[1]) % 2)

# Two commuting involutions (a concrete V4 representation).
J = sp.Matrix([[1, 0], [0, -1]])      # J^2 = I
E = sp.Matrix([[-1, 0], [0, 1]])       # ε^2 = I and Jε = εJ
I2 = sp.eye(2)

# Check involution/commutation relations
assert J * J == I2
assert E * E == I2
assert J * E == E * J


def rho(g):
    if g == (0, 0):
        return I2
    if g == (1, 0):
        return J
    if g == (0, 1):
        return E
    return J * E

# Optional: verify action law rho(a+b)=rho(a)rho(b) on this concrete model.
for a in V4:
    for b in V4:
        assert rho(v4_mul(a, b)) == rho(a) * rho(b)

# Generic anomaly deltaK
f11, f12, f21, f22 = sp.symbols("f11 f12 f21 f22")
delta = sp.Matrix([[f11, f12], [f21, f22]])

# V4 cross-cap and compatibility constraints:
# Cross-cap: ε δ ε = -δ
# Compatibility: ε δ = δ ε (equiv. to εδ ε = δ for involutional ε)
h_cross = sp.expand(E * delta * E + delta)
h_auto = sp.expand(E * delta - delta * E)

sol_cross = sp.solve(sp.Matrix(h_cross).reshape(4, 1), [f11, f12, f21, f22], dict=True)
sol_auto = sp.solve(sp.Matrix(h_auto).reshape(4, 1), [f11, f12, f21, f22], dict=True)
sol_both = sp.solve(sp.Matrix(list(h_cross) + list(h_auto)).reshape(8, 1), [f11, f12, f21, f22], dict=True)

print("compat solutions:", sol_auto)
print("cross-cap solutions:", sol_cross)
print("simultaneous solutions:", sol_both)

# Sample substitution sanity
for vals in [{f11: 0, f12: 1, f21: 2, f22: 3}, {f11: 0, f12: 0, f21: 0, f22: 0}, {f11: 5, f12: -1, f21: 7, f22: 9}]:
    d = delta.subs(vals)
    print("sample", vals, "cross residual", (E*d*E + d), "auto residual", (E*d - d*E))

# Algebraic certificate: from cross-cap + automorphism both enforced
assert sol_both == [{f11: 0, f12: 0, f21: 0, f22: 0}]

print("KleinFourAnomalyCancellation.py: V4 action consistency + cross-cap force δK = 0")
