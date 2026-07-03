g2two = 12096
derived = 6048
pgl = 5616
splitCarrier = 256
if splitCarrier != 2^8 then error "split carrier cardinality failed"
if g2two != 2^6*(2^6-1)*(2^2-1) then error "G2(2) order formula failed"
if derived*2 != g2two then error "derived half-order failed"
if pgl == g2two then error "PGL3(3) order separation failed"
print "MACAULAY2_G2TWO_SPLIT_ZORN_OK"

