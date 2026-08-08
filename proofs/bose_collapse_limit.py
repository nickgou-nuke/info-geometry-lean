# bose_collapse_limit.py
# Symbolically evaluate thermodynamic limits as radiation density rho -> infinity

import sympy as sp

# Variables
rho, A, B12, B21, N = sp.symbols('rho A B12 B21 N', positive=True, real=True)
N1, N2 = sp.symbols('N1 N2')

# Einstein relations state B12 = B21 (for non-degenerate levels)
# Rate equation at steady state: N2 * (A + B21 * rho) = N1 * B12 * rho
# Total population: N = N1 + N2

eq1 = sp.Eq(N1 + N2, N)
eq2 = sp.Eq(N2 * (A + B21 * rho), N1 * B12 * rho)

# Solve for N1, N2
solutions = sp.solve([eq1, eq2], (N1, N2))

N1_sol = solutions[N1]
N2_sol = solutions[N2]

print("Exact steady state solutions:")
print(f"N1 (Ground State, N_g): {N1_sol}")
print(f"N2 (Excited State, N_e): {N2_sol}")

# Apply Einstein relation B12 = B21
N1_sol = N1_sol.subs(B12, B21)
N2_sol = N2_sol.subs(B12, B21)

# Evaluate thermodynamic limit as rho -> infinity
limit_N1 = sp.limit(N1_sol, rho, sp.oo)
limit_N2 = sp.limit(N2_sol, rho, sp.oo)

print("\nThermodynamic limit as radiation density rho -> infinity:")
print(f"lim N_g: {limit_N1}")
print(f"lim N_e: {limit_N2}")

if limit_N1 == limit_N2:
    print("\nProof successful: Equalization of population states N_g = N_e as rho -> oo.")
else:
    print("\nProof failed.")
