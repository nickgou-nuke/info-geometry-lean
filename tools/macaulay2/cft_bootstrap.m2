-- cft_bootstrap.m2
R = ZZ
S = matrix(R, {{0, -1}, {1, 0}})
T = matrix(R, {{1, 1}, {0, 1}})
ST = S * T
M = ST^3
I2 = matrix(R, {{1, 0}, {0, 1}})

assert(M == -I2)
print "Success: (S*T)^3 == -I"
exit 0
