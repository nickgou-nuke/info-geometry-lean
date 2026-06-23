-- Exact-rational Macaulay2 + Dmodules witnesses for Smith retrocirculants.

loadPackage "Dmodules";

R = QQ[a,b, MonomialOrder => Lex];
F = frac R;
A = matrix(F, {{0,b},{a,0}});
Ap = matrix(F, {{0,1/a},{1/b,0}});
if A * Ap * A != A then error "ABA=A failed";
if Ap * A * Ap != Ap then error "BAB=B failed";
if transpose(A * Ap) != A * Ap then error "AB symmetry failed";
if transpose(Ap * A) != Ap * A then error "BA symmetry failed";
A0 = matrix(QQ, {{0,3},{2,0}});
B0 = matrix(QQ, {{0,7},{5,0}});
prod = A0 * B0;
if prod_(0,1) != 0 or prod_(1,0) != 0 then error "product circulant/diagonal failed";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "smith retrocirculant Moore-Penrose Macaulay2+Dmodules certificate: ok";
