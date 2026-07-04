-- tomita_dmodule.m2
needsPackage "Dmodules"
-- Weyl algebra
W = QQ[x,y,t,dx,dy,dt, WeylAlgebra => {{x,dx}, {y,dy}, {t,dt}}]
-- Modular operator Delta = S^* S
-- Holonomic D-module representing the modular operator
I = ideal(x*dx + y*dy - t*dt, dx^2 + dy^2 - dt^2)
print "Ideal I defined."
b = betti res I
print b
exit()
