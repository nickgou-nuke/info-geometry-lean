import sympy as sp
phi = (1 + sp.sqrt(5)) / 2
F = sp.Matrix([[1/phi, sp.sqrt(1/phi)], [sp.sqrt(1/phi), -1/phi]])

# Test standard phases: exp(4*pi*i/5), exp(-3*pi*i/5)
R1 = sp.Matrix([[sp.exp(sp.I * 4 * sp.pi / 5), 0], [0, sp.exp(-sp.I * 3 * sp.pi / 5)]])
sigma_1 = R1
sigma_2 = sp.simplify(F * R1 * F)
if sp.simplify(sigma_1 * sigma_2 * sigma_1 - sigma_2 * sigma_1 * sigma_2) == sp.zeros(2):
    print("R1 works")

# Test alternative phases: exp(-4*pi*i/5), exp(3*pi*i/5)
R2 = sp.Matrix([[sp.exp(-sp.I * 4 * sp.pi / 5), 0], [0, sp.exp(sp.I * 3 * sp.pi / 5)]])
sigma_1 = R2
sigma_2 = sp.simplify(F * R2 * F)
if sp.simplify(sigma_1 * sigma_2 * sigma_1 - sigma_2 * sigma_1 * sigma_2) == sp.zeros(2):
    print("R2 works")
