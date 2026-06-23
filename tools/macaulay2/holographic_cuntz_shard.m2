-- Exact-rational Macaulay2 + Dmodules audit for the finite holographic
-- Cuntz shard algebra.

needsPackage "Dmodules"

print "=== Holographic Cuntz shard Macaulay2 audit ==="

S = matrix(QQ, {{0,1},{0,0}});
T = matrix(QQ, {{0,0},{1,0}});
Psource = matrix(QQ, {{0,0},{0,1}});
Paperture = matrix(QQ, {{1,0},{0,0}});
I2 = id_(QQ^2);

if transpose(S) * S != Psource then error "source projection failed";
if S * transpose(S) != Paperture then error "aperture projection failed";
if transpose(T) * T != Paperture then error "complement source projection failed";
if Psource * Psource != Psource then error "source idempotence failed";
if Paperture * Paperture != Paperture then error "aperture idempotence failed";
if Psource + Paperture != I2 then error "source partition failed";
if Paperture == I2 then error "aperture should be proper";
if S * transpose(S) * S != S then error "partial isometry failed";

-- Dmodules lane: explicitly load and use the Weyl algebra. The finite aperture
-- x1 = 0 gives a holonomic boundary module for the one-coordinate readout.
W = makeWA(QQ[x0, x1]);
D0 = W_2;
D1 = W_3;
J = ideal(x1, D0, D1);
if isHolonomic(W^1 / J) != true then error "Dmodules aperture module failed";

print "HOLOGRAPHIC_CUNTZ_SHARD_MACAULAY2_DMODULES_AUDIT_OK";
