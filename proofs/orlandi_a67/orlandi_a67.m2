tauAs=7/10
tauSe=13/10
b1As=13/10
b1Se=1
b2As=(81/10)/1000000
b2Se=(17/10)/1000000
assert(tauSe/tauAs == 13/7)
assert(b1As/b1Se == 13/10)
assert(b2As/b2Se == 81/17)
assert(b2As-b2Se == (32/5)/1000000)
print "OK"
