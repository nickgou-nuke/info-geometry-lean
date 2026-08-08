# maxcal_free_energy.sage
# Formulation of Jaynes' Maximum Caliber (MaxCal) principle

print("Initializing Maximum Caliber Formalism...")
var('t, x, v, lambda_x, lambda_v')
# Phase space variables
x = function('x')(t)
v = diff(x, t)

# Action and Free Energy formulation
m, gamma, k = var('m, gamma, k')
L = 0.5 * m * v^2 - 0.5 * k * x^2
# Dissipation term in path integral via caliber
caliber = L - lambda_x * x - lambda_v * v

print("Caliber expression: ", caliber)

# Euler-Lagrange equations for MaxCal
EL_eq = diff(diff(caliber, v), t) - diff(caliber, x) == 0
print("Euler-Lagrange equations for Maximum Caliber:")
print(EL_eq)
