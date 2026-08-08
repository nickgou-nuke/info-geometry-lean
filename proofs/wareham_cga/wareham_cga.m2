needsPackage "Dmodules"
R = QQ[x1,x2,x3,y1,y2,y3,l]
qX = x1^2+x2^2+x3^2
qY = y1^2+y2^2+y3^2
FdotF = qX - qX
FdotG = x1*y1+x2*y2+x3*y3 - (1/2)*qX - (1/2)*qY
Distance = FdotG + (1/2)*((x1-y1)^2+(x2-y2)^2+(x3-y3)^2)
DilationNull = l^2*qX - l^2*qX
assert(FdotF == 0)
assert(Distance == 0)
assert(DilationNull == 0)
W = QQ[x1,x2,x3,D1,D2,D3, WeylAlgebra => {x1=>D1,x2=>D2,x3=>D3}]
Euler = x1*D1 + x2*D2 + x3*D3
NullConeDmodule = ideal(Euler)
assert(numgens NullConeDmodule == 1)
print "OK"
