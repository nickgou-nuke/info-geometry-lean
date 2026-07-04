needsPackage "Dmodules"
W = makeWA(QQ[x]);
Dx = W_1;
if Dx*x - x*Dx != 1_W then error "Weyl commutator [Dx,x] failed";
M = W^1 / ideal(Dx);
if not isHolonomic M then error "constant Weyl module should be holonomic";
print "MACAULAY2_DMODULES_PRIMON_CRYSTALLIZATION_SYNTHESIS_HOLONOMIC_OK";
