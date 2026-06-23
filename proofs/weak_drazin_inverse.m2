-- Exact-rational Macaulay2 + Dmodules certificate for weak Drazin inverses.

loadPackage "Dmodules";

A = matrix(QQ, {{2,0,0},{0,0,1},{0,0,0}});
Bmin = matrix(QQ, {{1/2,0,0},{0,0,0},{0,0,0}});
Bpoly = (1/2) * id_(QQ^3);
k = 2;
if Bmin * (A^(k+1)) != A^k then error "minimal weak Drazin check failed";
if Bpoly * (A^(k+1)) != A^k then error "polynomial weak Drazin check failed";
if A * Bpoly != Bpoly * A then error "commuting check failed";
R = QQ[x];
charPolyWeakDrazin = det(x * id_(R^3) - sub(A,R));
if charPolyWeakDrazin != x^2 * (x - 2) then error "characteristic polynomial mismatch";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "weak Drazin Macaulay2+Dmodules certificate: ok";
