import sympy as sp
phi = (1 + sp.sqrt(5)) / 2
F = sp.Matrix([
    [1/phi, 1/sp.sqrt(phi)],
    [1/sp.sqrt(phi), -1/phi]
])
I2 = sp.eye(2)
print("F*F - I2 is zero:", sp.simplify(F*F - I2) == sp.zeros(2, 2))

R1 = sp.exp(4*sp.pi*sp.I/5)
Rtau = sp.exp(-3*sp.pi*sp.I/5)
R = sp.diag(R1, Rtau)
print("R*R.H - I2 is zero:", sp.simplify(R*R.H - I2) == sp.zeros(2, 2))

sigma1 = R
sigma2 = F * R * F
ybe = sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2
ybe_simp = sp.simplify(ybe)
print("YBE is zero:", ybe_simp == sp.zeros(2, 2))
