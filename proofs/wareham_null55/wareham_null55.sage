e=vector(QQ,[1,0]); eb=vector(QQ,[0,1]); n=vector(QQ,[1,1]); nb=vector(QQ,[1,-1])
def q(x): return x[0]^2-x[1]^2
def b(x,y): return x[0]*y[0]-x[1]*y[1]
def refl(x): return vector(QQ,[-x[0],x[1]])
assert q(e)==1
assert q(eb)==-1
assert b(e,eb)==0
assert q(n)==0
assert q(nb)==0
assert b(n,nb)==2
assert refl(n)==-nb
assert refl(nb)==-n
m0=QQ(0); dP=QQ(1)/4; dT=QQ(1)/25
ms=m0*m0+dP+dT; mc=m0*m0+dP-dT
assert ms-mc==2*dT
assert ms!=mc
print((q(n),q(nb),b(n,nb),refl(n),ms-mc))
