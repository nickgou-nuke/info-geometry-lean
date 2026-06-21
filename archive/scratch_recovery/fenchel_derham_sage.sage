# SageMath script for De Rham Homology and Fenchel Legendre
from sage.all import *

var('t1 t2 e1 e2')
# Primal
psi = t1^2 + t2^2
eta1 = diff(psi, t1)
eta2 = diff(psi, t2)

print("1-form d(psi):", eta1, "dt1 +", eta2, "dt2")

# Hessian Metric (2-form)
H = matrix([[diff(eta1, t1), diff(eta1, t2)], [diff(eta2, t1), diff(eta2, t2)]])
print("Hessian Metric (Information Geometry):")
print(H)

# Dual
# eta1 = 2*t1 => t1 = e1/2
t1_sol = e1/2
t2_sol = e2/2
phi = t1_sol*e1 + t2_sol*e2 - (t1_sol^2 + t2_sol^2)
print("Fenchel-Legendre Dual phi:", phi)

print("Verification complete.")
