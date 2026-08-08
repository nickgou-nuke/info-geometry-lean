from sage.all import *

print("=== Exploring O(5,5) and its Lie Algebra (Type D5) ===")

# The Lie algebra so(5,5) is the split real form of the complex Lie algebra of type D5
L = LieAlgebra(QQ, cartan_type="D5")
print(f"Dimension of D5 Lie algebra: {L.dimension()}")

# Root system and Weyl group properties
rs = RootSystem("D5")
ambient = rs.ambient_space()
W = ambient.weyl_group()

print(f"\nRoot System: {rs}")
print(f"Weyl Group Size: {W.cardinality()} (which is 2^4 * 5! = 1920)")

print("\nCartan Matrix for D5:")
print(rs.cartan_matrix())

print(f"\nNumber of positive roots: 20 (computed by n(n-1) for D5)")
print("Total number of roots: 40")

# Pin(5,5) is the double cover. The center of the Spin(10) / Spin(5,5) group is related to the weight lattice.
P = rs.weight_lattice()
Q = rs.root_lattice()
print(f"\nIndex of Root Lattice in Weight Lattice (Size of Center of Spin/Pin group): {P.index_in(Q)}")

print("\n=== Exploration Complete ===")
