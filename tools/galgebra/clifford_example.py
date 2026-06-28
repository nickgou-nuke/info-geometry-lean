#!/usr/bin/env python3
"""
GalaClifford example: Clifford algebra Cl(2,0) and its relation to the
spin representation, which underlies the hyperkahler structure of
Hilb_n(C^2).
"""

from galgebra.ga import Ga

# Define a 2-dimensional Euclidean vector space with basis (e1, e2)
# Clifford algebra Cl(2,0): e1^2 = 1, e2^2 = 1, e1*e2 = -e2*e1
(ga, e1, e2) = Ga.build('e1 e2', g=[1,1])

print("Clifford algebra Cl(2,0) basis:")
print("1 (grade 0)")
print("e1, e2 (grade 1)")
print("e12 = e1*e2 (grade 2)")
e12 = e1 * e2
print("e1*e2 =", e12)
print("(e1*e2)^2 =", e12 * e12)

# Show that the even subalgebra is spanned by 1 and e1*e2
print("\nEven subalgebra basis: 1, e1*e2")
print("Any even element: a + b*(e1*e2) for a,b in the base field.")

# Compute the commutator and anticommutator
print("\nCommutator [e1, e2] = e1*e2 - e2*e1 =", e1*e2 - e2*e1)
print("Anticommutator {e1, e2} = e1*e2 + e2*e1 =", e1*e2 + e2*e1)
# Should be 0 and 2*e1*e2? Actually {e1,e2}=0 for orthogonal basis? Wait:
# For orthogonal basis, e_i*e_j + e_j*e_i = 2*g_{ij}.
# Since g_{12}=0, we expect {e1,e2}=0.
print("Expected anticommutator: 0 (since e1 and e2 are orthogonal)")

# The even subalgebra is isomorphic to the complex numbers via
# 1 -> 1, e1*e2 -> i (since (e1*e2)^2 = -1)
print("\n(e1*e2)^2 =", e12 * e12, "which should be -1")
print("Thus e1*e2 behaves like the imaginary unit i.")

# Now, the geometric algebra of R^2 with this Clifford algebra contains
# the spin group Spin(2) = U(1), which acts on the space of spinors.
# This underlies the complex structure on the hyperkahler manifold
# Hilb_n(C^2) (which is actually holomorphic symplectic, not hyperkahler?
# Hilb_n(C^2) is hyperkahler of complex dimension 2n, with three complex
# structures satisfying the quaternion relations.)

print("\nThis illustrates the algebraic origin of the complex structure")
print("on the hyperkahler manifold via the Clifford algebra.")