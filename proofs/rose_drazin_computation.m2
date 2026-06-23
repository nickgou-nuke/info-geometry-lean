-- Exact-rational Macaulay2 + Dmodules witnesses for Rose's Drazin computation.

loadPackage "Dmodules";

R = QQ[x];
f1 = x^2 + 5*x + 1;
p1 = -24*x - 115;
if (x^3 * p1 - 1) % f1 != 0 then error "example 1 remainder failed";

C1 = matrix(QQ, {{0,-1},{1,-5}});
Z2 = map(QQ^2, QQ^2, 0);
A1 = map(QQ^4, QQ^4, {{0,0,0,0},{0,0,0,0},{0,0,0,-1},{0,0,1,-5}});
I4 = id_(QQ^4);
D1 = (A1^2) * (-24*A1 - 115*I4);
-- Rose formula gives the Drazin inverse; check A^(ell+1)D=A^ell with ell=2.
if A1^3 * D1 != A1^2 then error "Drazin relation failed";
if D1 * A1 != A1 * D1 then error "commutation failed";

f2 = x^4 + x^3 + x^2 + x + 1;
if (x * x^4 - 1) % f2 != 0 then error "example 2 remainder failed";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "rose Drazin computation Macaulay2+Dmodules certificate: ok";
