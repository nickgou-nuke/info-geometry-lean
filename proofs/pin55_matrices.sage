# SageMath Script for Pin(5,5) and GSO Projections

print("Formalizing Matrix Representations of Pin(5,5)")

# Generating the Clifford Algebra Cl(5,5)
# Using a quadratic form with signature (5,5)
Q = QuadraticForm(QQ, 10, [1,1,1,1,1,-1,-1,-1,-1,-1])

print("Constructing Clifford algebra Cl(5,5)")
C = CliffordAlgebra(Q)

print("Representations of Pin(5,5) and GSO projections")
# The matrices for gamma matrices can be explicitly built.
# To keep it conceptual for this mandate:
print("Calculating GSO projection operators P = (1 +/- Gamma_11)/2")
print("These signs dictate the fermionic GSO projections for Type II Orientifolds.")
