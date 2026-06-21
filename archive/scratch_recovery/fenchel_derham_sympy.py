import sympy as sp

# De Rham Cohomology & Information Geometry Metric using SymPy

theta1, theta2 = sp.symbols('theta1 theta2', real=True)
eta1, eta2 = sp.symbols('eta1 eta2', real=True)

# Primal Log-Generating Potential
Q = sp.exp(theta1**2 + theta2**2)
psi = sp.log(Q)

# 1-form differential (Score / Thermodynamic Force)
d_psi_1 = sp.diff(psi, theta1)
d_psi_2 = sp.diff(psi, theta2)

print(f"1-form d(psi): eta1 = {d_psi_1}, eta2 = {d_psi_2}")

# 2-form Information Geometry Metric (Hessian)
H11 = sp.diff(d_psi_1, theta1)
H12 = sp.diff(d_psi_1, theta2)
H21 = sp.diff(d_psi_2, theta1)
H22 = sp.diff(d_psi_2, theta2)

print(f"2-form Hessian Metric: [[{H11}, {H12}], [{H21}, {H22}]]")

# Fenchel-Legendre Dual Potential
# phi(eta) = theta * eta - psi(theta)
# Solve eta_i = d_psi_i for theta_i
theta1_sol = sp.solve(eta1 - d_psi_1, theta1)[0]
theta2_sol = sp.solve(eta2 - d_psi_2, theta2)[0]

phi = theta1_sol * eta1 + theta2_sol * eta2 - psi.subs({theta1: theta1_sol, theta2: theta2_sol})
phi = sp.simplify(phi)
print(f"Fenchel-Legendre Dual phi(eta): {phi}")

# Verify d_phi(eta) = theta
d_phi_1 = sp.diff(phi, eta1)
d_phi_2 = sp.diff(phi, eta2)
print(f"Dual 1-form d(phi): theta1 = {d_phi_1}, theta2 = {d_phi_2}")
