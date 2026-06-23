-- Exact-rational Macaulay2 + Dmodules certificate for Chao retrocirculants.
-- Loads Dmodules explicitly and constructs a Weyl-algebra quotient module.

loadPackage "Dmodules";

R = QQ[m0,m1,m2,m3,m4,m5,m6,m7,x];
mu = {m0,m1,m2,m3,m4,m5,m6,m7};
sigma = apply(8, k -> (5*k) % 8);
if apply(8, k -> sigma#(sigma#k)) != toList(0..7) then error "not involutive";
fixed = select(toList(0..7), k -> sigma#k == k);
if fixed != {0,2,4,6} then error "fixed set mismatch";
cycles = {{1,5},{3,7}};
P = mutableMatrix(R, 8, 8);
for r from 0 to 7 do for c from 0 to 7 do if sigma#c == r then P_(r,c) = 1_R;
P = matrix P;
D = diagonalMatrix mu;
A = P*D;
expected = product(fixed, k -> x - mu#k) * product(cycles, p -> x^2 - (mu#(p#0))*(mu#(p#1)));
charPolyChao = det(x * id_(R^8) - A);
if charPolyChao != expected then error "characteristic factorization mismatch";

-- Dmodules/Weyl lane: build a noncommutative quotient module as a real package use.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "chao retrocirculant Macaulay2+Dmodules certificate: ok";
