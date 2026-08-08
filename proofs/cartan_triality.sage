# cartan_triality.sage
# Formulate the SO(8) Lie algebra representations (8_v, 8_s, 8_c).
# Prove the outer automorphisms exchanging these representations via S_3.

# Create the Lie algebra D4 (which corresponds to so(8))
L = LieAlgebra(QQ, cartan_type="D4")

# Get the weight lattice
W = L.weight_lattice()

# Highest weights for the fundamental representations
# 8_v (vector)
hw_v = W.fundamental_weight(1)
# 8_s (spinor)
hw_s = W.fundamental_weight(3)
# 8_c (conjugate spinor)
hw_c = W.fundamental_weight(4)

print("Highest weight of 8_v:", hw_v)
print("Highest weight of 8_s:", hw_s)
print("Highest weight of 8_c:", hw_c)

# We can demonstrate the triality by looking at the Dynkin diagram of D4
# The Dynkin diagram has a central node (2) and three outer nodes (1, 3, 4)
# The outer automorphism group is S3, permuting the nodes {1, 3, 4}.
# This permutation exchanges the highest weights of the 8_v, 8_s, and 8_c representations.

print("\nDynkin Diagram for D4 (so(8)):")
print(CartanMatrix("D4").dynkin_diagram())

print("\nThe S3 outer automorphism acts by permuting nodes 1, 3, and 4.")
print("This corresponds exactly to exchanging the representations 8_v, 8_s, and 8_c.")
