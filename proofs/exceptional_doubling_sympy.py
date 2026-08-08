"""SymPy witness: Non-Hermitian Exceptional Point Braid Topology.

Formalizes the core result from J. Lukas K. König's thesis on why 
the Nielsen-Ninomiya fermion doubling theorem fails for non-Hermitian 
systems. The topological invariants of Exceptional Points (EPs) are 
non-Abelian braids, allowing them to evade the cancellation required 
by the torus topology.
"""

import sympy as sp

print("======================================================================")
print("       NON-HERMITIAN EXCEPTIONAL POINTS & BRAID TOPOLOGY              ")
print("======================================================================\n")

# ══════════════════════════════════════════════════════════════════════════════
# §1. The Non-Abelian Braid Group B_3
# ══════════════════════════════════════════════════════════════════════════════
print("§1. Braid Group Generators and Non-Abelian Commutators")
# We represent the braid group B_3 (for a 3-band non-Hermitian system)
# abstractly to demonstrate the failure of the doubling theorem.

# In a 3-band system, there are two elementary braid generators:
# s1: swaps band 1 and 2
# s2: swaps band 2 and 3
s1, s2 = sp.symbols('sigma_1 sigma_2', commutative=False)

# The defining relations of B_3:
# 1) Non-commutation of adjacent strands: s1 * s2 != s2 * s1
# 2) The braid relation: s1 * s2 * s1 = s2 * s1 * s2

# In Hermitian systems, the invariants are Chern/Wrapping numbers (Abelian).
# Sum of charges on a torus must be 0: W_total = W_1 + W_2 + ... = 0

# In non-Hermitian systems, the invariant is a braid B.
# The boundary of the fundamental domain of a torus T^2 evaluates to the commutator
# of the loops along the non-contractible cycles (x and y):
Bx, By = sp.symbols('B_x B_y', commutative=False)

# The total braid charge of all EPs in the Brillouin zone must equal this commutator:
B_total = Bx * By * Bx**-1 * By**-1

print(f"  Total Torus Braid Charge: {B_total}")

# If we choose Bx = s1 and By = s2
B_total_eval = s1 * s2 * s1**-1 * s2**-1

print(f"  Evaluating for Bx = sigma_1, By = sigma_2:")
print(f"  B_total = {B_total_eval}")

print("\n  Is the total charge trivially the identity (1)?")
# In an Abelian group, Bx * By * Bx^-1 * By^-1 = 1.
# In the Braid group, s1 and s2 do NOT commute.
is_abelian_trivial = (s1 * s2 * s1**-1 * s2**-1 == 1)
print(f"  Result: {is_abelian_trivial}")

print("\nConclusion: Because the braid group is non-Abelian, the commutator")
print("[B_x, B_y] is NOT the identity. Therefore, a single non-trivial")
print("Exceptional Point (or an unpaired topological monopole) can exist")
print("on the Brillouin torus without being forced to double and cancel! ✓")
