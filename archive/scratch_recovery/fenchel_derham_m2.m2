load "Dmodules.m2"
-- Define the Weyl algebra over Q
W = QQ[x,y, dx, dy, WeylAlgebra=>{x=>dx, y=>dy}]
-- The potential Q
Q = x^2 + y^2
-- The D-module annihilating 1/Q replaces the complex loop integral
-- by algebraically defining the poles of d ln Q
I = ann (1/Q)
print "The D-module annihilating 1/Q (poles of d ln Q):"
print I
exit(0)
