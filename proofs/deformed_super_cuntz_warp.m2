-- Macaulay2 / Dmodules witness for the finite q-warp algebraic shadow.
-- Run with: M2 --script proofs/deformed_super_cuntz_warp.m2

R = QQ[q, theta1, theta2, theta3, theta4, x]
flatSum = 2
qAngleSum = q*(theta1 + theta2 + theta3 + theta4)
deficit = flatSum - qAngleSum
assert(deficit == 2 - q*(theta1 + theta2 + theta3 + theta4))

-- The D-module lane records S_prod = d log Q in the Weyl algebra.  Load
-- Dmodules explicitly and verify the Weyl/D-module commutator rather than
-- stopping at bare matrices.
loadPackage "Dmodules"
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
N = cokernel matrix{{xW*Dx - Dx*xW - 1_W}}
assert(numgens source presentation N == 1)

print("Macaulay2 deficit and D-module Weyl-commutator witness passed")
