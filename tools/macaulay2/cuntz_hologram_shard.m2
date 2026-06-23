-- Macaulay2 exact-rational certificate for the finite Cuntz hologram shard lane.
-- Run with: M2 --script tools/macaulay2/cuntz_hologram_shard.m2

Sleft = matrix {{1_QQ,0},{0,1},{0,0},{0,0}}
Sright = matrix {{0_QQ,0},{0,0},{1,0},{0,1}}
I2 = id_(QQ^2)
I4 = id_(QQ^4)

assert(transpose Sleft * Sleft == I2)
assert(transpose Sright * Sright == I2)
assert(transpose Sleft * Sright == matrix {{0_QQ,0},{0,0}})
assert(transpose Sright * Sleft == matrix {{0_QQ,0},{0,0}})
print "PASS: branch isometries and orthogonality"

Pleft = Sleft * transpose Sleft
Pright = Sright * transpose Sright
assert(Pleft + Pright == I4)
print "PASS: branch range projections sum to identity"

needsPackage "Dmodules";
W = makeWA(QQ[x]);
xW = W_0; Dx = W_1;
assert(Dx*xW - xW*Dx == 1_W);
print "PASS: Dmodules Weyl commutator [Dx,x] = 1";
print "CUNTZ_HOLOGRAM_SHARD_MACAULAY2_OK";
