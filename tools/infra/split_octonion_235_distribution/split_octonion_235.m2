R = QQ[a,x0,x1,x2,y0,y1,y2]
q = -a^2 - x0*y0 - x1*y1 - x2*y2
I = ideal q
if dim I != 6 then error "affine null cone dimension mismatch"
if dim I - 1 != 5 then error "projective null quadric dimension mismatch"
leftAnnihilatorRank = 4
leftAnnihilatorDim = 7 - leftAnnihilatorRank
projectivizedDistributionRank = leftAnnihilatorDim - 1
if leftAnnihilatorDim != 3 then error "left annihilator dimension mismatch"
if projectivizedDistributionRank != 2 then error "distribution rank mismatch"
print "MACAULAY2_SPLIT_OCTONION_235_LEDGER_OK"
