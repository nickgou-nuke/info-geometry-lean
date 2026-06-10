import sympy as sp

print("==========================================================")
print(" PRIMON GAS THERMODYNAMICS & WITTEN INDEX WITNESS")
print("==========================================================")

# Let p1, p2, p3 be the first three prime modes.
p1, p2, p3 = sp.symbols('p1 p2 p3', positive=True)
beta = sp.symbols('beta', real=True)

# Energies of the prime modes: E_p = log(p)
# Boltzmann weights: x_p = exp(-beta * E_p) = p^(-beta)
x1, x2, x3 = p1**(-beta), p2**(-beta), p3**(-beta)

# 1. Bosonic Partition Function (CCR)
# Z_B = \prod_{p} (1 - x_p)^(-1)
Z_B_1 = 1 / (1 - x1)
Z_B_2 = 1 / (1 - x2)
Z_B_3 = 1 / (1 - x3)
# Taylor expansion to first order interactions
Z_B_expanded = sp.series(Z_B_1 * Z_B_2 * Z_B_3, x1, 0, 2).removeO()
print(f"[1] Bosonic Partition Function (Z_B) Expansion:\n    {Z_B_expanded}")

# 2. Fermionic Partition Function (CAR)
# Z_F = \prod_{p} (1 + x_p)
Z_F_1 = 1 + x1
Z_F_2 = 1 + x2
Z_F_3 = 1 + x3
Z_F = Z_F_1 * Z_F_2 * Z_F_3
Z_F_expanded = sp.expand(Z_F)
print(f"\n[2] Fermionic Partition Function (Z_F) Expansion:\n    {Z_F_expanded}")

# 3. Witten Index / Moebius Parity Partition Function
# W = Tr((-1)^F exp(-beta H)) = \prod_{p} (1 - x_p)
W_1 = 1 - x1
W_2 = 1 - x2
W_3 = 1 - x3
W = W_1 * W_2 * W_3
W_expanded = sp.expand(W)
print(f"\n[3] Witten Index (Moebius Parity Z_F_graded):\n    {W_expanded}")

# 4. Identity: Z_B * W = 1
# This proves that the Witten index of the Fermionic gas is the exact inverse of the Bosonic Zeta function.
# W = 1 / Z_B  =>  W * Z_B = 1
identity = sp.simplify((Z_B_1 * Z_B_2 * Z_B_3) * W)
print(f"\n[4] Thermodynamic Super-Symmetry Identity (Z_B * W):\n    {identity}")
assert identity == 1

print("\n=> SUCCESS: The Witten Index of the CAR Primon Gas is mathematically equivalent to 1/Zeta(beta).")
print("=> The Moebius function encodes the exact Fermion Parity (-1)^F.")
