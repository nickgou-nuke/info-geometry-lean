-- Macaulay2 / Dmodules certificate for Greville 1973 Souriau--Frame Drazin algebra.
-- Run with: M2 --script tools/macaulay2/greville1973_souriau_frame_drazin.m2

A = matrix {{0_QQ,1,0},{0,0,0},{0,0,2}}
I3 = id_(QQ^3)

trace3 = M -> M_(0,0) + M_(1,1) + M_(2,2)

B0 = I3
p1 = trace3(A*B0)
B1 = A*B0 - p1*I3
p2 = (1/2) * trace3(A*B1)
B2 = A*B1 - p2*I3
p3 = (1/3) * trace3(A*B2)
B3 = A*B2 - p3*I3

assert(p1 == 2)
assert(p2 == 0)
assert(p3 == 0)
assert(B2 != 0)
assert(B3 == 0)
print "PASS: Souriau--Frame recurrence has r=3, s=1, k=2"

k = 2
X = (p1 ^ (-(k + 1))) * (A^k) * (B0^(k+1))
Expected = matrix {{0_QQ,0,0},{0,0,0},{0,0,1/2}}
assert(X == Expected)
print "PASS: Greville formula gives A^D"

assert(A*X == X*A)
assert(X*A*X == X)
assert(A^(k+1)*X == A^k)
assert(A*X*X == X)
print "PASS: Drazin index-2 laws"

Regular = A*X
Nilpotent = I3 - Regular
assert(Regular == matrix {{0_QQ,0,0},{0,0,0},{0,0,1}})
assert(Nilpotent == matrix {{1_QQ,0,0},{0,1,0},{0,0,0}})
assert(Regular^2 == Regular)
assert(Nilpotent^2 == Nilpotent)
assert((A*Nilpotent)^2 == 0)
print "PASS: Drazin projectors split the regular and nilpotent lanes"

P = matrix {{0_QQ,0,1},{0,1,0},{1,0,0}}
Pinv = inverse P
Ac = P*A*Pinv
Xc = P*X*Pinv
assert(Ac*Xc == Xc*Ac)
assert(Xc*Ac*Xc == Xc)
assert(Ac^(k+1)*Xc == Ac^k)
print "PASS: GL_3(Q) conjugation preserves the packet"

-- Dmodules lane: explicitly load Dmodules and verify the Weyl algebra
-- commutator used by Souriau--Frame differential characteristic calculations.
needsPackage "Dmodules"
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "GREVILLE1973_MACAULAY2_DMODULES_CERTIFICATE_OK"
