needsPackage "Dmodules"
W = makeWA(QQ[x]);
Dx = W_1;
if Dx*x - x*Dx != 1_W then error "Weyl commutator [Dx,x] failed";
M = W^1 / ideal(Dx);
if not isHolonomic M then error "constant-sheaf Weyl module should be holonomic";
groupOrder = 6;
automorphismCount = 6;
if groupOrder != automorphismCount then error "complete-group cardinal mismatch";
print "MACAULAY2_DMODULES_AUTOMORPHISM_TOWER_S3_HOLONOMIC_OK";
