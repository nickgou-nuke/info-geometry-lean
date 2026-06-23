-- Macaulay2 / Dmodules exact-rational certificate for holographic
-- tensor-factor separation.
-- Run with: M2 --script tools/macaulay2/holographic_tensor_factor_separation.m2

needsPackage "Dmodules"

assertZero = (M, label) -> (
  assert(M == map(target M, source M, 0));
  print concatenate("PASS: ", label)
)

comm = (A, B) -> A*B - B*A

Eta = matrix {
  {1_QQ,0,0,0,0,0,0,0,0,0},
  {0_QQ,1,0,0,0,0,0,0,0,0},
  {0_QQ,0,1,0,0,0,0,0,0,0},
  {0_QQ,0,0,1,0,0,0,0,0,0},
  {0_QQ,0,0,0,1,0,0,0,0,0},
  {0_QQ,0,0,0,0,-1,0,0,0,0},
  {0_QQ,0,0,0,0,0,-1,0,0,0},
  {0_QQ,0,0,0,0,0,0,-1,0,0},
  {0_QQ,0,0,0,0,0,0,0,-1,0},
  {0_QQ,0,0,0,0,0,0,0,0,-1}
}
Parity = -id_(QQ^10)
B = matrix {
  {1_QQ,0,0,0,0,0,2/3,0,0,0},
  {0_QQ,1,0,0,0,-2/3,0,0,0,0},
  {0_QQ,0,1,0,0,0,0,0,0,0},
  {0_QQ,0,0,1,0,0,0,0,0,0},
  {0_QQ,0,0,0,1,0,0,0,0,0},
  {0_QQ,0,0,0,0,1,0,0,0,0},
  {0_QQ,0,0,0,0,0,1,0,0,0},
  {0_QQ,0,0,0,0,0,0,1,0,0},
  {0_QQ,0,0,0,0,0,0,0,1,0},
  {0_QQ,0,0,0,0,0,0,0,0,1}
}

E12 = matrix {{0_QQ,1,0},{0,0,0},{0,0,0}}
E21 = matrix {{0_QQ,0,0},{1,0,0},{0,0,0}}
E23 = matrix {{0_QQ,0,0},{0,0,1},{0,0,0}}
E32 = matrix {{0_QQ,0,0},{0,0,0},{0,1,0}}
E13 = matrix {{0_QQ,0,1},{0,0,0},{0,0,0}}
E31 = matrix {{0_QQ,0,0},{0,0,0},{1,0,0}}
H1 = matrix {{1_QQ,0,0},{0,-1,0},{0,0,0}}
H2 = matrix {{0_QQ,0,0},{0,1,0},{0,0,-1}}

for G in {Eta,Parity,B} do (
  for C in {E12,E21,E23,E32,E13,E31,H1,H2} do (
    assertZero(comm(G ** id_(QQ^3), id_(QQ^10) ** C), "G tensor C commutator")
  )
)

Twist = matrix {{0_QQ,-1},{1,0}}
Glide = matrix {{1_QQ,0},{0,-1}}
TwistLift = Twist ** id_(QQ^3)
GlideLift = Glide ** id_(QQ^3)
assert(TwistLift*TwistLift == -id_(QQ^6))
assert(GlideLift*GlideLift == id_(QQ^6))
assertZero(GlideLift*TwistLift + TwistLift*GlideLift, "lifted Brillouin anticommutator")

for C in {E12,E21,E23,E32,E13,E31,H1,H2} do (
  assertZero(comm(TwistLift, id_(QQ^2) ** C), "twist tensor C commutator");
  assertZero(comm(GlideLift, id_(QQ^2) ** C), "glide tensor C commutator")
)

W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "HOLOGRAPHIC_TENSOR_FACTOR_SEPARATION_MACAULAY2_DMODULES_CERTIFICATE_OK"
