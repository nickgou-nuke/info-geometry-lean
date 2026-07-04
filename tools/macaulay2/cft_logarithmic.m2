R = QQ[h]
L0 = matrix {{h, 1}, {0, h}}
I2 = id_(R^2)
M = L0 - h*I2
M2 = M^2
assert(M2 == 0)
print "Success: (L0 - h*I2)^2 == 0"
