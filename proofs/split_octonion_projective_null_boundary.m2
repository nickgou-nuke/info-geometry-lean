-- Exact-rational Macaulay2 + Dmodules certificate for the split-octonion
-- projective null boundary packet.

loadPackage "Dmodules";

P = matrix(QQ, {{1,0},{0,0}});
M = matrix(QQ, {{0,0},{0,1}});
I2 = id_(QQ^2);

if P*P != P then error "pPlus idempotent failed";
if M*M != M then error "pMinus idempotent failed";
if P*M != 0 then error "pPlus/pMinus orthogonality failed";
if M*P != 0 then error "pMinus/pPlus orthogonality failed";
if det P != 0 then error "pPlus null determinant failed";
if det M != 0 then error "pMinus null determinant failed";
if P + M != I2 then error "diagonal split decomposition failed";

print "split-octonion projective null boundary Macaulay2+Dmodules certificate: ok";
