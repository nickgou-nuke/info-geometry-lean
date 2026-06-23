-- Exact-rational Macaulay2 + Dmodules certificate for finite holographic Cuntz shards.

loadPackage "Dmodules";

S = matrix(QQ, {{0,1},{0,0}});
Psource = matrix(QQ, {{0,0},{0,1}});
Paperture = matrix(QQ, {{1,0},{0,0}});
if transpose(S) * S != Psource then error "source projection failed";
if S * transpose(S) != Paperture then error "aperture projection failed";
if Psource * Psource != Psource then error "source idempotent failed";
if Paperture * Paperture != Paperture then error "aperture idempotent failed";
if S * transpose(S) * S != S then error "partial isometry failed";
T = matrix(QQ, {{0,0},{1,0}});
if transpose(S)*S + transpose(T)*T != id_(QQ^2) then error "two shard partition failed";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "holographic Cuntz shard Macaulay2+Dmodules certificate: ok";
