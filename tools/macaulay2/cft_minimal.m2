p = 4_QQ
q = 3_QQ
C = 1_QQ - 6_QQ*(p-q)^2/(p*q)
assert(C == 1/2)
print "C is exactly 1/2"
