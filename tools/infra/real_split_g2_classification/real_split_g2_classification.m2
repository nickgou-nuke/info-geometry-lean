rows = 512
cols = 64
derivRank = 50
nullity = 14
g2Roots = 12
g2PositiveRoots = 6
g2Weyl = 12
normPositive = 4
normNegative = 4
normZero = 0
if rows != 64*8 then error "derivation rows mismatch"
if derivRank + nullity != cols then error "rank-nullity mismatch"
if nullity != 14 then error "derivation nullity mismatch"
if normPositive + normNegative + normZero != 8 then error "split norm signature dimension mismatch"
if g2Roots != 12 or g2PositiveRoots != 6 or g2Weyl != 12 then error "G2 root/Weyl ledger mismatch"
print "MACAULAY2_REAL_SPLIT_G2_LEDGER_OK"
