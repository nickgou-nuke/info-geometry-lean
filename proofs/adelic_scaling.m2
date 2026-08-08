-- Macaulay2: D-modules for the scaling operator
needsPackage "Dmodules"

R = QQ[x]
W = makeWeylAlgebra(R)

-- Variables in W are x and dx
-- Define the Euler operator
eulerOp = x * dx
-- Define the shifted operator
shiftedOp = x * dx + 1/2

print("Euler Operator x*dx:")
print(eulerOp)

print("Shifted Operator x*dx + 1/2:")
print(shiftedOp)

-- The symmetric part is fixed at 1/2 I due to the Weyl algebra commutation
comm = x*dx - dx*x
print("Commutator [x, dx] = ")
print(comm)

print("The +1/2 Jacobian shift precisely balances the commutator -1, ensuring symmetry.")
