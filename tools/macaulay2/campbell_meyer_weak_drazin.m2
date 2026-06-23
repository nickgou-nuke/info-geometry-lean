-- Macaulay2 / Dmodules certificate for Campbell--Meyer 1978 weak Drazin inverses.
-- Run with: M2 --script tools/macaulay2/campbell_meyer_weak_drazin.m2

assertWeak = (A, B, k, label) -> (
  assert(B * (A^(k + 1)) == A^k);
  print concatenate("PASS: ", label)
)

assertDrazin = (A, D, k, label) -> (
  assert(A*D == D*A);
  assert(D*A*D == D);
  assert((A^(k + 1))*D == A^k);
  print concatenate("PASS: ", label)
)

A = matrix {{2_QQ,0,0},{0,0,1},{0,0,0}}
Nil = matrix {{0_QQ,0,0},{0,0,1},{0,0,0}}
I3 = id_(QQ^3)
assert(Nil^2 == 0)
assert(A^3 == 2 * A^2)

D = matrix {{1/2_QQ,0,0},{0,0,0},{0,0,0}}
assertDrazin(A, D, 2, "Drazin inverse")
assertWeak(A, D, 2, "Drazin inverse is weak")

Wild = matrix {{1/2_QQ,3,5},{0,7,11},{0,13,17}}
assertWeak(A, Wild, 2, "wild weak inverse")
assert(Wild != D)
assert(A*Wild != Wild*A)

Poly = (1/2_QQ) * I3
assertWeak(A, Poly, 2, "polynomial/Souriau-Frame weak inverse")
assert(A*Poly == Poly*A)
assert(det Poly == 1/8_QQ)
p1 = trace(A*I3)
assert(p1 == 2)
assert((1/p1) * I3 == Poly)
assert(Poly != D)

ProjectiveWeak = matrix {{1/2_QQ,2,3},{0,0,5},{0,0,7}}
assertWeak(A, ProjectiveWeak, 2, "projective-shaped weak inverse")
BA = ProjectiveWeak*A
assert(BA == matrix {{1_QQ,0,2},{0,0,0},{0,0,0}})
assert(BA^2 == BA)

Comm = matrix {{1/2_QQ,0,0},{0,3,4},{0,0,3}}
assertWeak(A, Comm, 2, "commuting weak inverse")
assert(A*Comm == Comm*A)

P = matrix {{0_QQ,0,1},{0,1,0},{1,0,0}}
assertWeak(P*A*P, P*Poly*P, 2, "GL_3(Q) conjugate")

-- Dmodules lane: explicitly load Dmodules and verify the Weyl algebra
-- commutator used by differential-operator weak-Drazin certificates.
needsPackage "Dmodules"
W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "CAMPBELL_MEYER_WEAK_DRAZIN_MACAULAY2_DMODULES_CERTIFICATE_OK"
