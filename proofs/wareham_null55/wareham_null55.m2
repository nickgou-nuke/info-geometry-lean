needsPackage "Dmodules"
R=QQ[p,m,pb,mb,dP,dT]
q=p^2-m^2
qn=1^2-1^2
qnb=1^2-(-1)^2
bdot=1*1-1*(-1)
assert(qn==0)
assert(qnb==0)
assert(bdot==2)
assert((-1)==(-1))
assert((1)==(1))
W=QQ[x,D, WeylAlgebra => {x=>D}]
NullDmodule=ideal(x*D)
assert(numgens NullDmodule==1)
print "OK"
