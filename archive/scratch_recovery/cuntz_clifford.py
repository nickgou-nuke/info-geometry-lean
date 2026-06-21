import clifford as cf
import numpy as np

# We can construct the CAR algebra for N fermions using a Clifford algebra of dimension 2N
# Let's do N = 2, so Cl(2, 2)
layout, blades = cf.Cl(2, 2)

# Basis vectors are e1, e2, e3, e4
# e1^2 = 1, e2^2 = 1
# e3^2 = -1, e4^2 = -1

# Fermionic creation/annihilation operators can be built from orthogonal basis
# a_1 = (e_1 + e_3) / 2
# a_1^* = (e_1 - e_3) / 2
# a_2 = (e_2 + e_4) / 2
# a_2^* = (e_2 - e_4) / 2

e1 = blades['e1']
e2 = blades['e2']
e3 = blades['e3']
e4 = blades['e4']

a1 = 0.5 * (e1 + e3)
a1_star = 0.5 * (e1 - e3)

a2 = 0.5 * (e2 + e4)
a2_star = 0.5 * (e2 - e4)

# Commutators in Clifford algebra are defined using geometric product or inner product
def anticommutator(A, B):
    return A * B + B * A

print("a1 a1^* + a1^* a1 =", anticommutator(a1, a1_star))
print("a1 a2^* + a2^* a1 =", anticommutator(a1, a2_star))
print("a1 a1 + a1 a1 =", anticommutator(a1, a1))

# These should be 1, 0, and 0.
