needsPackage "Dmodules"
R = QQ[x, y, dx, dy, WeylAlgebra => {x=>dx, y=>dy}]
-- This quotient imposes square-zero relations on two Weyl-algebra generators.
-- Those relations alone do not define a Klein quadric or prove on-shell factorization.
I = ideal(dx^2, dy^2)
M = R^1 / I
print("=== Macaulay2 D-modules Klein Witness ===")
print("Holonomic rank for nilpotent Klein constraints: " | toString(holonomicRank M))
print("Square-zero generator quotient computed; no Klein-quadric or on-shell factorization theorem is tested.")
exit
