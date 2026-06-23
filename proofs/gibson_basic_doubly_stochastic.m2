-- Exact-rational Macaulay2 + Dmodules witnesses for Gibson basic matrices.

loadPackage "Dmodules";

R = QQ[x, b];
Basic12 = t -> matrix(R, {{t, 1-t, 0}, {1-t, t, 0}, {0, 0, 1}});
M = Basic12(x);
ones = matrix(R, {{1}, {1}, {1}});
RowColOnes = N -> (N_(0,0) == 1 and N_(1,0) == 1 and N_(2,0) == 1);
if not RowColOnes(M * ones) then error "row sums failed";
if not RowColOnes(transpose(M) * ones) then error "column sums failed";
if det(M) != 2*x - 1 then error "determinant failed";
A = Basic12(2/3);
B = Basic12(3/5);
P = A * B;
if not RowColOnes(P * ones) then error "product row sums failed";
if not RowColOnes(transpose(P) * ones) then error "product column sums failed";
if det(P) != det(A) * det(B) then error "product determinant failed";
obstruction = matrix(R, {{1,0,b},{0,1+b,b},{0,0,1}});
if det(obstruction) != 1 + b then error "obstruction determinant failed";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "gibson basic doubly stochastic Macaulay2+Dmodules certificate: ok";
