# causal_tripotent.sage
# Tripotent Projectors of the Causal Light Cone in Cl(1,1)

# Define the Clifford algebra Cl(1,1)
Q = QuadraticForm(QQ, 2, [1, 0, -1])
Cl = CliffordAlgebra(Q)

# Generators
e0, e1 = Cl.gens()

# Tripotent projectors P+, P-, P0
# P+ for Causal Future J+
P_plus = (1 + e0) / 2

# P- for Causal Past J-
P_minus = (1 - e0) / 2

# P0 for Null Boundary (spatially degenerate in this simplified algebraic representation)
# In Cl(1,1), e0^2 = 1, e1^2 = -1. 
# Tripotent operators satisfy P^3 = P.
# For a null element n = e0 + e1, n^2 = 0.
P_0 = e0 * e1

print("Tripotent Projectors generated:")
print(f"P+ (Causal Future): {P_plus}")
print(f"P- (Causal Past): {P_minus}")
print(f"P0 (Null Boundary): {P_0}")

# Verifying tripotency for P_plus and P_minus (P^3 = P)
assert P_plus^3 == P_plus
assert P_minus^3 == P_minus
print("Tripotency verified for P+ and P-.")
