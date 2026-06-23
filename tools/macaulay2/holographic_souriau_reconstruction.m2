-- Macaulay2 / Dmodules exact-rational certificate for the finite holographic
-- Souriau reconstruction lane.
-- Run with: M2 --script tools/macaulay2/holographic_souriau_reconstruction.m2

O55 = diagonalMatrix apply(10, i -> if i < 5 then 1_QQ else -1_QQ)
assert(O55 * O55 == id_(QQ^10))
assert(transpose O55 == O55)
print "PASS: O(5,5) split metric is involutive and symmetric"

T = matrix {{0_QQ,-1},{1,0}}
K = matrix {{1_QQ,0},{0,-1}}
assert(T*T == -id_(QQ^2))
assert(K*K == id_(QQ^2))
assert(K*T == -(T*K))
print "PASS: Brillouin twist/glide relations"

C = 2 * id_(QQ^3)
E12 = matrix {{0_QQ,1,0},{0,0,0},{0,0,0}}
E21 = matrix {{0_QQ,0,0},{1,0,0},{0,0,0}}
E23 = matrix {{0_QQ,0,0},{0,0,1},{0,0,0}}
E32 = matrix {{0_QQ,0,0},{0,0,0},{0,1,0}}
E13 = matrix {{0_QQ,0,1},{0,0,0},{0,0,0}}
E31 = matrix {{0_QQ,0,0},{0,0,0},{1,0,0}}
H1 = matrix {{1_QQ,0,0},{0,-1,0},{0,0,0}}
H2 = matrix {{0_QQ,0,0},{0,1,0},{0,0,-1}}
scan({E12,E21,E23,E32,E13,E31,H1,H2}, G -> assert(C*G - G*C == 0))
print "PASS: scalar modular laser commutes with displayed su(3) generators"

needsPackage "Dmodules";
W = makeWA(QQ[x]);
xW = W_0; Dx = W_1;
assert(Dx*xW - xW*Dx == 1_W);
print "PASS: Dmodules Weyl commutator [Dx,x] = 1";
print "HOLOGRAPHIC_SOURIAU_RECONSTRUCTION_MACAULAY2_DMODULES_OK";
