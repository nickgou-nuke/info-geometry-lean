# SageMath verification of Clifford equivalence
Q = QuadraticForm(RR, 2, [1, 0, 1])
Cl = CliffordAlgebra(Q)
e1, e2 = Cl.gens()
S = e1 * e2
assert S^2 == -1
print("SageMath: Clifford equivalence S^2 = -1 verified successfully.")
