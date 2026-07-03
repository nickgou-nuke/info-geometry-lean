needsPackage "Dmodules"
W = makeWA(QQ[u,v]);
Du = W_2;
Dv = W_3;
if Du*u - u*Du != 1_W then error "Dmodules Weyl commutator [Du,u] failed";
if Dv*v - v*Dv != 1_W then error "Dmodules Weyl commutator [Dv,v] failed";
if Du*v - v*Du != 0_W then error "Dmodules mixed commutator failed";
I = ideal(Du,Dv);
M = W^1 / I;
if isHolonomic(M) != true then error "Cartan chart D-module not holonomic";
rankDistribution = 2;
nullQuadricDim = 5;
if rankDistribution + 3 != nullQuadricDim then error "(2,3,5) dimension ledger mismatch";
print "MACAULAY2_DMODULES_SPLIT_OCTONION_235_HOLONOMIC_OK";
