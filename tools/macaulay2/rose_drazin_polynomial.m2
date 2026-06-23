-- Macaulay2 / Dmodules exact-rational audit for Rose 1976.
-- Run with: M2 --script tools/macaulay2/rose_drazin_polynomial.m2

needsPackage "Dmodules"

assertZero = (M, label) -> (
  if M != 0 then error(label | " failed")
)

N = matrix {{0_QQ, 1}, {0, 0}}
C = matrix {{0_QQ, -1}, {1, -5}}
Z2 = map(QQ^2, QQ^2, 0)
A = directSum(N, C)
I2 = id_(QQ^2)
I4 = id_(QQ^4)

assertZero(N^2, "N^2 = 0")
assertZero(C^2 + 5*C + I2, "C^2+5C+I=0")

X = A^2 * (-24*A - 115*I4)
Expected = directSum(Z2, -C - 5*I2)
assertZero(X - Expected, "Rose polynomial equals block Drazin candidate")

assertZero(A*X - X*A, "A X = X A")
assertZero(X*A*X - X, "X A X = X")
assertZero(A^3*X - A^2, "A^(k+1) X = A^k")

W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "ROSE1976_MACAULAY2_DMODULES_AUDIT_OK"
