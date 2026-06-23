-- Macaulay2 / Dmodules certificate for Hartwig 1976 SVD / Moore-Penrose
-- inverses of bordered matrices.
-- Run with: M2 --script tools/macaulay2/hartwig1976_svd_mp_border.m2

assertMP = (A, X, label) -> (
  assert(A*X*A == A);
  assert(X*A*X == X);
  assert(transpose(A*X) == A*X);
  assert(transpose(X*A) == X*A);
  print concatenate("PASS: ", label)
)

baseA = matrix {{2_QQ,0},{0,0}}
baseMP = matrix {{1/2_QQ,0},{0,0}}
assertMP(baseA, baseMP, "base SVD block")

case1 = matrix {{2_QQ,0,3},{0,0,0},{1,0,5}}
case1MP = matrix {{5/7_QQ,0,-3/7_QQ},{0,0,0},{-1/7_QQ,0,2/7_QQ}}
z = 5_QQ - 1_QQ * (1/2_QQ) * 3_QQ
assert(z == 7/2_QQ)
assertMP(case1, case1MP, "Hartwig Case 1 border")
assertMP(matrix {{7/5_QQ,0},{0,0}}, matrix {{5/7_QQ,0},{0,0}},
  "Hartwig Case 1 Schur complement")

case3 = matrix {{2_QQ,0,0},{0,0,1},{0,1,5}}
case3MP = matrix {{1/2_QQ,0,0},{0,-5,1},{0,1,0}}
assertMP(case3, case3MP, "Hartwig Case 3 border")
assertMP(matrix {{2_QQ,0},{0,-1/5_QQ}}, matrix {{1/2_QQ,0},{0,-5}},
  "Hartwig Case 3 Schur complement")

P = matrix {{0_QQ,0,1},{0,1,0},{1,0,0}}
assert(transpose(P) * P == id_(QQ^3))
assertMP(P * case1 * transpose(P), P * case1MP * transpose(P),
  "orthogonal GL_3(Q) conjugate")

-- Dmodules lane: explicitly load Dmodules and check the Weyl algebra
-- commutator used by differential-operator Schur/SVD certificates.
needsPackage "Dmodules"
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "HARTWIG1976_SVD_MP_BORDER_MACAULAY2_DMODULES_CERTIFICATE_OK"
