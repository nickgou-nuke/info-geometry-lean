-- Macaulay2 polynomial verifier for Zorn determinant ratio / scalar-flow identities.
-- Scaled determinants are derived from scaled Zorn coordinates.
R = QQ[a,b,u1,u2,u3,v1,v2,v3,c,d,x1,x2,x3,y1,y2,y3,r,s,t]
normZ = (A,B,U1,U2,U3,V1,V2,V3) -> A*B - (U1*V1 + U2*V2 + U3*V3)
NX = normZ(a,b,u1,u2,u3,v1,v2,v3)
NY = normZ(c,d,x1,x2,x3,y1,y2,y3)
NrX = normZ(r*a,r*b,r*u1,r*u2,r*u3,r*v1,r*v2,r*v3)
NrY = normZ(r*c,r*d,r*x1,r*x2,r*x3,r*y1,r*y2,r*y3)
NsX = normZ(s*a,s*b,s*u1,s*u2,s*u3,s*v1,s*v2,s*v3)
NtY = normZ(t*c,t*d,t*x1,t*x2,t*x3,t*y1,t*y2,t*y3)
scaleX = NrX - r^2 * NX
scaleY = NrY - r^2 * NY
common = NrY*NX - NY*NrX
unequal = s^2*NtY*NX - t^2*NY*NsX
if scaleX != 0 then error "N(scale_r(X)) = r^2 N(X) failed"
if scaleY != 0 then error "N(scale_r(Y)) = r^2 N(Y) failed"
if common != 0 then error "common-scaling determinant ratio invariant failed"
if unequal != 0 then error "unequal-scaling determinant ratio factor failed"
print "PASS: N(scale_r(X)) = r^2 N(X)"
print "PASS: N(scale_r(Y)) = r^2 N(Y)"
print "PASS: common-scaling determinant ratio invariant"
print "PASS: unequal-scaling determinant ratio factor"
print "ZORN_DETERMINANT_RATIO_FLOW_SCALING_OK"
