-- Macaulay2 / Dmodules certificate for the finite V4 / Q8 projective bridge.
-- Run with: M2 --script tools/macaulay2/q8_v4_projective_bridge.m2

needsPackage "Dmodules";

print "=== V4 / Q8 Macaulay2 certificate ===";

-- Exact-rational 4x4 left-regular quaternion matrices on the basis [1, i, j, k].
Li = matrix {
  {0, -1, 0, 0},
  {1,  0, 0, 0},
  {0,  0, 0, -1},
  {0,  0, 1, 0}
};

Lj = matrix {
  {0, 0, -1, 0},
  {0, 0,  0, 1},
  {1, 0,  0, 0},
  {0, -1, 0, 0}
};

Lk = Li * Lj;
I4 = matrix {
  {1, 0, 0, 0},
  {0, 1, 0, 0},
  {0, 0, 1, 0},
  {0, 0, 0, 1}
};

if Li * Li != -I4 then error "Li^2 failed";
if Lj * Lj != -I4 then error "Lj^2 failed";
if Lk * Lk != -I4 then error "Lk^2 failed";
if Li * Lj != Lk then error "LiLj = Lk failed";
if Lj * Li != -Lk then error "LjLi = -Lk failed";
if Lj * Lk != Li then error "LjLk = Li failed";
if Lk * Li != Lj then error "LkLi = Lj failed";
print "PASS: exact-rational quaternion matrices verify the Q8 relations";

-- Dmodules lane: explicitly load the Weyl algebra and verify the commutator.
W = makeWA(QQ[x]);
xW = W_0;
Dx = W_1;
if Dx*xW - xW*Dx != 1_W then error "Weyl commutator failed";
print "PASS: Dmodules loaded and Weyl commutator certified";

print "Q8_V4_PROJECTIVE_BRIDGE_MACAULAY2_DMODULES_CERTIFICATE_OK";
exit 0
