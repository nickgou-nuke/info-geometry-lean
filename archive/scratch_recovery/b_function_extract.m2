needsPackage "Dmodules"
W = QQ[x,y, Dx, Dy, WeylAlgebra => {x=>Dx, y=>Dy}]
Q = x^2 + y^2
bPoly = globalBFunction(Q)
print("--- Bernstein-Sato Invariant Isolated ---")
print("b(s) = " | toString(bPoly))
exit(0)
