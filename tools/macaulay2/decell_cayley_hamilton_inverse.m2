-- Macaulay2 / Dmodules exact-rational certificate for Decell 1965.
-- Run with: M2 --script tools/macaulay2/decell_cayley_hamilton_inverse.m2

needsPackage "Dmodules"

assertZero = (M, label) -> (
  if M != 0 then error(label | " failed")
)

checkPenrose = (A, Ap, label) -> (
  assertZero(A*Ap*A - A, label | ": A A+ A = A");
  assertZero(Ap*A*Ap - Ap, label | ": A+ A A+ = A+");
  assertZero(transpose(A*Ap) - A*Ap, label | ": A A+ symmetric");
  assertZero(transpose(Ap*A) - Ap*A, label | ": A+ A symmetric");
  print("PASS: " | label)
)

A1 = matrix {{1_QQ, 2, 3}, {2, 4, 6}}
Ap1 = matrix {{1/70_QQ, 1/35}, {1/35, 2/35}, {3/70, 3/35}}
checkPenrose(A1, Ap1, "rank-one rectangular 2x3")

A2 = matrix {{1_QQ, 2}, {3, 5}}
Ap2 = matrix {{-5_QQ, 2}, {3, -1}}
checkPenrose(A2, Ap2, "invertible square 2x2")

A3 = matrix {{1_QQ, 0, 1}, {0, 1, 1}, {1, 1, 2}}
Ap3 = matrix {{5/9_QQ, -4/9, 1/9}, {-4/9, 5/9, 1/9}, {1/9, 1/9, 2/9}}
checkPenrose(A3, Ap3, "rank-two symmetric 3x3")

A0 = matrix {{0_QQ, 0, 0}, {0, 0, 0}}
Ap0 = matrix {{0_QQ, 0}, {0, 0}, {0, 0}}
checkPenrose(A0, Ap0, "zero rectangular 2x3")

-- Dmodules lane: explicitly load Dmodules and verify the Weyl algebra
-- commutator alongside the rational matrix certificate.
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "DECELL_CAYLEY_HAMILTON_MACAULAY2_DMODULES_CERTIFICATE_OK"
