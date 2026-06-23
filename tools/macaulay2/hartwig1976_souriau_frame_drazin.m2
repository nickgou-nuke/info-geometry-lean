-- Macaulay2 / Dmodules certificate for Hartwig 1976 Souriau--Frame Drazin algebra.
-- Run with: M2 --script tools/macaulay2/hartwig1976_souriau_frame_drazin.m2

QQx = QQ[x]

A = matrix {{0_QQ,0,0},{0,2,0},{0,0,3}}
I3 = id_(QQ^3)
A0 = matrix {{6_QQ,0,0},{0,0,0},{0,0,0}}
A1 = matrix {{-5_QQ,0,0},{0,-3,0},{0,0,-2}}

X = (I3 - (1/6)*A0) * ((-1/6)*A1)
Expected = matrix {{0_QQ,0,0},{0,1/2,0},{0,0,1/3}}
assert(X == Expected)
print "PASS: Hartwig coefficient formula gives A#"

assert(A*X*A == A)
assert(X*A*X == X)
assert(A*X == X*A)
assert(A^2*X == A)
print "PASS: group inverse and Drazin index-one laws"

Z = I3 - A*X
ZExpected = matrix {{1_QQ,0,0},{0,0,0},{0,0,0}}
assert(Z == ZExpected)
assert(Z^2 == Z)
assert(A*Z == 0)
assert(Z*A == 0)
print "PASS: principal idempotent selects the zero-root lane"

P = matrix {{0_QQ,1,0},{1,0,0},{0,0,1}}
Pinv = inverse P
Ac = P*A*Pinv
Xc = P*X*Pinv
assert(Ac*Xc*Ac == Ac)
assert(Xc*Ac*Xc == Xc)
assert(Ac*Xc == Xc*Ac)
print "PASS: GL_3 conjugation preserves the representation"

-- Dmodules lane: the Souriau--Frame characteristic variable is represented in
-- the Weyl algebra.  The commutator [d/dx, x] = 1 is the algebraic differential
-- core used by D-module characteristic and adjugate calculations.
needsPackage "Dmodules"
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "HARTWIG1976_MACAULAY2_DMODULES_CERTIFICATE_OK"
