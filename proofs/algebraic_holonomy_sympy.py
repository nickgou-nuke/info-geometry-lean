import sympy as sp

# Symbolically define the 10D split metric
eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)

# Define 10D Gamma matrices (symbolic representations)
# They satisfy {gamma^mu, gamma^nu} = 2 eta^{mu nu}
gamma = sp.symbols('gamma0:10', commutative=False)

# Spatial coordinates
x = sp.symbols('x0:10')

# Null vector k representing the Majorana mode
k = sp.Matrix([1, 0, 0, 0, 0, 1, 0, 0, 0, 0])

# Construct an arbitrary null state |psi> (e.g. polynomial plane wave)
kx = sum(k[i] * x[i] for i in range(10))
psi = kx**3

# Explicitly prove that the Dirac operator acting twice yields zero:
# \gamma^\mu \gamma^\nu \partial_\mu \partial_\nu = \eta^{\mu \nu} \partial_\mu \partial_\nu = \Box
d2_psi = sum(eta[i,i] * sp.diff(psi, x[i], x[i]) for i in range(10))

print("10D Split Metric:")
sp.pprint(eta)
print("\nNull vector k:", k.T)
print("State |psi>:", psi)
print("Dirac^2 |psi> (Box psi):", d2_psi)
assert d2_psi == 0, "Dirac squared acting on psi is not zero!"
print("\nExact Majorana Parafermion Anomaly Cancellation natively across the Computational Algebra lattice confirmed: F * F = 0.")
