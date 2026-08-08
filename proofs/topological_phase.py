# topological_phase.py
# Symbolically evaluate the contour integral of the conformal flow over the zero modes,
# showing the extraction of the discrete topological phase.

import sympy as sp

print("Initializing SymPy for Conformal Flow Contour Integral...")

# Define variables
z = sp.Symbol('z', complex=True)
dz = sp.Symbol('dz')

# Define the conformal flow over zero modes
# We use a function with a pole to represent a zero mode at z_0
z_0 = sp.Symbol('z_0', complex=True)
f = 1 / (z - z_0)

print(f"Conformal flow function: f(z) = {f}")

# Extract the topological phase by integrating over a contour C enclosing z_0
# Using Cauchy's Integral Formula: \oint_C f(z) dz = 2 * pi * i * Res(f, z_0)

# Calculate the residue
residue = sp.residue(f, z, z_0)
print(f"Residue at z_0: {residue}")

# Evaluate the contour integral
contour_integral = 2 * sp.pi * sp.I * residue
print(f"Contour Integral evaluated: {contour_integral}")

# The discrete topological phase is extracted from the integral
phase = sp.exp(contour_integral)
print(f"Discrete Topological Phase extracted: {phase}")

# Consider a fractional phase from a branch cut, e.g. for Majorana fermions (sqrt(z))
# The logarithmic derivative is g(z) = 1/(2z)
theta = sp.Symbol('theta', real=True)
r = sp.Symbol('r', positive=True)

# Parametrize z = r * e^{i theta}
z_param = r * sp.exp(sp.I * theta)
dz_dtheta = sp.diff(z_param, theta)

g = 1 / (2 * z_param)
integrand = g * dz_dtheta

# Integrate from 0 to 2*pi
winding_integral = sp.integrate(integrand, (theta, 0, 2*sp.pi))
print(f"Monodromy integral for sqrt(z): {winding_integral}")

monodromy_phase = sp.exp(winding_integral)
print(f"Quantized Monodromy Phase: {monodromy_phase}")
