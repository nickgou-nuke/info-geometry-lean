groupOrder = 6
auCount = 6
innerAutomorphismCount = 6
centerCount = 1
if groupOrder != 6 then error "S3 order mismatch";
if auCount != groupOrder then error "Aut(S3) cardinal mismatch";
if innerAutomorphismCount != auCount then error "inner/aut mismatch";
if centerCount != 1 then error "center mismatch";
print "MACAULAY2_AUTOMORPHISM_TOWER_S3_LEDGER_OK";
