-- Macaulay2 witness for split Zorn null-boundary identities.
-- Dmodules is explicitly loaded to exercise the intended external lane.
needsPackage "Dmodules";
R = QQ[r,s,x1,x2,x3,y1,y2,y3,rr,ss,u1,u2,u3,v1,v2,v3];

detZ = Z -> (
  Z#0*Z#1 - (Z#2*Z#5 + Z#3*Z#6 + Z#4*Z#7)
);

mulZ = (X,Y) -> (
  {
    X#0*Y#0 + (X#2*Y#5 + X#3*Y#6 + X#4*Y#7),
    (X#5*Y#2 + X#6*Y#3 + X#7*Y#4) + X#1*Y#1,
    X#0*Y#2 + Y#1*X#2 - (X#6*Y#7 - X#7*Y#6),
    X#0*Y#3 + Y#1*X#3 - (X#7*Y#5 - X#5*Y#7),
    X#0*Y#4 + Y#1*X#4 - (X#5*Y#6 - X#6*Y#5),
    Y#0*X#5 + X#1*Y#5 + (X#3*Y#4 - X#4*Y#3),
    Y#0*X#6 + X#1*Y#6 + (X#4*Y#2 - X#2*Y#4),
    Y#0*X#7 + X#1*Y#7 + (X#2*Y#3 - X#3*Y#2)
  }
);

X = {r,s,x1,x2,x3,y1,y2,y3};
Y = {rr,ss,u1,u2,u3,v1,v2,v3};
assert(detZ(mulZ(X,Y)) - detZ(X)*detZ(Y) == 0);
n = {0_R,0_R,1_R,0_R,0_R,0_R,0_R,0_R};
z = {0_R,0_R,0_R,0_R,0_R,0_R,0_R,0_R};
assert(detZ(n) == 0);
assert(mulZ(n,n) == z);
print "split_zorn_null_boundary.m2: checks passed";
