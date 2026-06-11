import sympy as sp

# 4x4 active projector (activates 3 levels, 1 level is the zero/vacuum sector)
P_active = sp.Matrix([
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 0]
])

# 4x4 zero projector
Z_4 = sp.zeros(4, 4)

# 8x8 Dirac-Hodge operator (hopping between physical and ghost sheets)
# O = [0, P_active]
#     [P_active, 0]
O = sp.BlockMatrix([
    [Z_4, P_active],
    [P_active, Z_4]
]).as_explicit()

print("Supercharge Operator O (8x8):")
sp.pprint(O)

print("\nO^3 == O :", O**3 == O)

# Drazin Support Projector P_D = O^2
P_D = O**2
print("\nDrazin Support Projector P_D = O^2:")
sp.pprint(P_D)

# Drazin Null Projector P_zero = I - P_D
I_8 = sp.eye(8)
P_zero = I_8 - P_D
print("\nDrazin Null Projector P_zero = I - O^2:")
sp.pprint(P_zero)

print("\nCheck: O * P_zero == 0 :", O * P_zero == sp.zeros(8, 8))
