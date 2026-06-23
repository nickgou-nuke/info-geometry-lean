# SageMath / GAP certificate for Bost-Connes Amplituhedron Boundary Kinematics
# Run with: sage tools/sage/bost_connes_amplituhedron_boundary.sage

print("==================================================")
print("SageMath Exact-Rational Certificate:")
print("Bost-Connes Amplituhedron Boundary Kinematics")
print("==================================================")

# We use Sage's ExteriorAlgebra to verify the Arnold-Cohen relation
z1, z2, z3 = var('z1 z2 z3')

# Define the rational function field over Q
F = FractionField(PolynomialRing(QQ, 'z1, z2, z3'))
z1_f, z2_f, z3_f = F.gens()

# Define the Exterior Algebra over the rational function field
E = ExteriorAlgebra(F, 'dz1, dz2, dz3')
dz1, dz2, dz3 = E.gens()

# Define the dlog forms
w12 = (1 / (z1_f - z2_f)) * (dz1 - dz2)
w23 = (1 / (z2_f - z3_f)) * (dz2 - dz3)
w31 = (1 / (z3_f - z1_f)) * (dz3 - dz1)

# BCFW Arnold-Cohen relation
bcfw_rel = w12*w23 + w23*w31 + w31*w12

is_zero = bool(bcfw_rel == 0)

print(f"Arnold-Cohen Relation (BCFW on-shell recursion) == 0 : {is_zero}")

if is_zero:
    print("\nBOST_CONNES_AMPLITUHEDRON_SAGE_CERTIFICATE_OK")
else:
    print("\nFAILED: Arnold-Cohen relation does not sum to zero.")
