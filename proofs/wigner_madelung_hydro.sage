# wigner_madelung_hydro.sage
# Formulation of Wigner function and Madelung equations

print("Formalizing Wigner-Madelung Hydrodynamics...")

# Define variables for phase space and wave function
var('x, p, t, hbar, m')
var('rho, S') # Madelung representation variables: psi = sqrt(rho) * exp(i * S / hbar)

# Wigner function definition (symbolic representation)
# W(x, p) = 1/(pi*hbar) \int \psi*(x+y) \psi(x-y) exp(2i p y / hbar) dy
# We focus on the resulting Madelung equations from the Schrodinger equation

# Schrodinger equation components mapping to Madelung Hydrodynamics
# \psi = \sqrt{\rho} e^{iS/\hbar}
# Substituting into i\hbar \partial_t \psi = (-\hbar^2/2m \nabla^2 + V)\psi
# Real part yields the Quantum Hamilton-Jacobi equation
# \partial_t S + (\nabla S)^2 / 2m + V + Q = 0
# where Q is the quantum potential.

# Define quantum potential Q symbolically
# Q = -\hbar^2 / (2m) * (\nabla^2 \sqrt{\rho}) / \sqrt{\rho}
# In 1D: \nabla^2 -> d^2/dx^2
rho_func = function('rho_func')(x, t)
sqrt_rho = sqrt(rho_func)

d1_sqrt_rho = diff(sqrt_rho, x)
d2_sqrt_rho = diff(d1_sqrt_rho, x)

Q = - (hbar^2 / (2*m)) * d2_sqrt_rho / sqrt_rho

print("Quantum Potential Q:")
print(Q.full_simplify())
