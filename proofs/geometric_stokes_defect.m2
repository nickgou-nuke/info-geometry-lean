-- Macaulay2/Dmodules certificate for the planar defect x^2+y^2.
-- This checks the Weyl lane and the Bernstein-Sato root at s=-1.
needsPackage "Dmodules";

W = QQ[x, y, dx, dy, WeylAlgebra => {x=>dx, y=>dy}];
assert(dx*x - x*dx == 1_W);
assert(dy*y - y*dy == 1_W);
assert(dx*y - y*dx == 0_W);

f = x^2 + y^2;
bf = globalBFunction(f);
-- For this smooth quadratic over QQ, the global b-function is (s+1)^2.
S = ring bf;
svar = S_0;
assert(bf == (svar + 1)^2);
assert(sub(bf, {svar => -1}) == 0);
print "geometric_stokes_defect.m2: Dmodules b-function and Weyl checks passed";
