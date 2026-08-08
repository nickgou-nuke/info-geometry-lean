r1, r2, nu1, nu2, rho, beta = var('r1 r2 nu1 nu2 rho beta')

# BPS Monopole limiting case for Harrington-Shepard calorons
def caloron_action_density(r1, r2, rho, beta):
    c1 = cosh(2 * pi * nu1 * r1)
    s1 = sinh(2 * pi * nu1 * r1)
    c2 = cosh(2 * pi * nu2 * r2)
    s2 = sinh(2 * pi * nu2 * r2)
    
    psi = -cos(2 * pi * beta) + c1 * c2 + ((r1**2 + r2**2 + pi**2 * rho**2)/(2*r1*r2))*s1*s2
    return psi

# High Temperature Limit (Debye Screening)
T, N_c, N_f = var('T N_c N_f')
debye_suppression = exp(-(1/3)*(2*N_c + N_f)*(pi*rho*T)**2)
