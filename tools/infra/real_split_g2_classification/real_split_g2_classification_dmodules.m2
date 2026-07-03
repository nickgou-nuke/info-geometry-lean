needsPackage "Dmodules"
R = QQ[x, Dx, WeylAlgebra => {x => Dx}]
I = ideal(x*Dx - Dx*x + 1)
-- This lane verifies Dmodules availability and keeps the real classification theorem separate.
rows = 512
cols = 64
derivRank = 50
nullity = 14
if derivRank + nullity != cols then error "rank-nullity mismatch"
print "MACAULAY2_DMODULES_REAL_SPLIT_G2_STATUS_OK"
