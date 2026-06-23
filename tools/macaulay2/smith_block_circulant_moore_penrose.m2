-- Macaulay2 / Dmodules exact-rational certificate for Smith 1977
-- block-circulant Moore-Penrose inverses.
-- Run with: M2 --script tools/macaulay2/smith_block_circulant_moore_penrose.m2

assertZero = (M, label) -> (
  assert(M == map(target M, source M, 0));
  print concatenate("PASS: ", label)
)

assertMP = (A, X, label) -> (
  assert(A*X*A == A);
  assert(X*A*X == X);
  assert(transpose(A*X) == A*X);
  assert(transpose(X*A) == X*A);
  print concatenate("PASS: ", label)
)

Q = matrix {
  {0_QQ,0,1,0,0,0},
  {0_QQ,0,0,1,0,0},
  {0_QQ,0,0,0,1,0},
  {0_QQ,0,0,0,0,1},
  {1_QQ,0,0,0,0,0},
  {0_QQ,1,0,0,0,0}
}

A = matrix {
  {1_QQ,0,1,0,0,0},
  {0_QQ,2,0,0,0,1},
  {0_QQ,0,1,0,1,0},
  {0_QQ,1,0,2,0,0},
  {1_QQ,0,0,0,1,0},
  {0_QQ,0,0,1,0,2}
}

Ap = matrix {
  {1/2_QQ,0,-1/2,0,1/2,0},
  {0_QQ,4/9,0,1/9,0,-2/9},
  {1/2_QQ,0,1/2,0,-1/2,0},
  {0_QQ,-2/9,0,4/9,0,1/9},
  {-1/2_QQ,0,1/2,0,1/2,0},
  {0_QQ,1/9,0,-2/9,0,4/9}
}

assert(det A == 18_QQ)
assertZero(A*Q - Q*A, "A commutes with Q tensor I2")
assertZero(Ap*Q - Q*Ap, "A+ commutes with Q tensor I2")
assert(A*Ap == id_(QQ^6))
assert(Ap*A == id_(QQ^6))
assertMP(A, Ap, "Smith 1977 rational block-circulant MP witness")

-- Dmodules lane: explicitly load Dmodules and verify the Weyl algebra
-- commutator beside the exact rational matrix certificate.
needsPackage "Dmodules"
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "SMITH1977_BLOCK_CIRCULANT_MACAULAY2_DMODULES_CERTIFICATE_OK"
