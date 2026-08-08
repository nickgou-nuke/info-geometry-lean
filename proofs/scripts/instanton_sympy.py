import sympy as sp

x, rho, g = sp.symbols('x rho g', positive=True, real=True)
Nc = sp.Symbol('N_c', integer=True, positive=True)

# BPST Instanton Action Density
action_density = (192 * rho**4) / (x**2 + rho**2)**4
S_0 = 8 * sp.pi**2 / g**2

# Tunneling rate (dilute gas approximation)
dn_I = (8 * sp.pi**2 / g**2)**(2*Nc) * sp.exp(-S_0) / rho**5

# Zero-mode profile
def zero_mode_profile(x_val, rho_val):
    return rho_val / (sp.pi * (x_val**2 + rho_val**2)**(1.5))
