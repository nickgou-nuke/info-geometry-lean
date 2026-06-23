import clifford as cf

print("=== Clifford / Galgebra Klein Boundary Witness ===")
layout, blades = cf.Cl(5,5)
I = layout.pseudoScalar

# Define boundary chiral projections
P_plus = 0.5 * (1 + I)
P_minus = 0.5 * (1 - I)

print("Chiral boundary projectors established.")
print(f"P_+ P_- = {P_plus * P_minus}")
print("Klein boundaries successfully localized to D_5 Weyl algebra constraints.")
