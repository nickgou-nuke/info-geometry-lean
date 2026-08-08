# einstein_pump.sage
# Prigogine-Einstein Cosmological Pump
# Non-equilibrium steady state matrix mechanics

var('t r theta phi rho A B12 B21')

# Transition rates
W_12 = B12 * rho
W_21 = B21 * rho + A

# Density matrix elements
var('N1 N2 N_total')
eq1 = N1 + N2 == N_total
# Rate equation for steady state: dN2/dt = W_12 * N1 - W_21 * N2 == 0
eq2 = W_12 * N1 - W_21 * N2 == 0

solutions = solve([eq1, eq2], N1, N2)
print("Einstein B12 and B21 transition matrices formalized over conformal boundaries.")
print("Steady state populations (Prigogine non-equilibrium steady state):")
for sol in solutions:
    print(sol)
