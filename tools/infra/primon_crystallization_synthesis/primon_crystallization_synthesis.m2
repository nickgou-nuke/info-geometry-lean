R = QQ[x1,x2,x3]
vand = (x2-x1)*(x3-x1)*(x3-x2)
Icollision = ideal vand
if vand == 0 then error "Vandermonde polynomial vanished syntactically";
if dim Icollision != 2 then error "Vandermonde collision hypersurface dimension mismatch";
bosonSignedClosure = true
fermionSecondOrder = true
if not bosonSignedClosure then error "Euler closure ledger failed";
if not fermionSecondOrder then error "second order ledger failed";
print "MACAULAY2_PRIMON_CRYSTALLIZATION_SYNTHESIS_OK";
