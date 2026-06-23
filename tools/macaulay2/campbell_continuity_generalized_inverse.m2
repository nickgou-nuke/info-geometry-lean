-- Macaulay2 / Dmodules exact-rational audit for Campbell 1977.
-- Run with: M2 --script tools/macaulay2/campbell_continuity_generalized_inverse.m2

needsPackage "Dmodules"

assertZero = (M, label) -> (
  if M != 0 then error(label | " failed")
)

absQQ = x -> if x < 0 then -x else x

oneNorm = M -> (
  cols := numColumns M;
  rows := numRows M;
  best := 0_QQ;
  for j from 0 to cols - 1 do (
    s := 0_QQ;
    for i from 0 to rows - 1 do s = s + absQQ(M_(i,j));
    if s > best then best = s;
  );
  best
)

A = matrix {{1_QQ, 2, 3}, {2, 4, 6}}
Ap = matrix {{1/70_QQ, 1/35}, {1/35, 2/35}, {3/70, 3/35}}
F = matrix {{1/100_QQ, 0}, {-1/150, 1/90}, {0, 1/120}}
X = Ap + F
Im = id_(QQ^2)
In = id_(QQ^3)
E1 = A*X*A - A
E2 = X*A*X - X
E3 = A*X - transpose(X)*transpose(A)
E4 = X*A - transpose(A)*transpose(X)
Rhs = Ap*E1*Ap + (In - Ap*A)*E4*Ap + Ap*E3*(Im - A*Ap) + (In - Ap*A)*(-E2 + E4*Ap*E3)*(Im - A*Ap)
assertZero(F - Rhs, "Moore-Penrose residual decomposition")
nE1 = oneNorm E1
nE2 = oneNorm E2
nE3 = oneNorm E3
nE4 = oneNorm E4
nAp = oneNorm Ap
nApA = oneNorm(Ap*A)
nLeftMP = oneNorm(In - Ap*A)
nRightMP = oneNorm(Im - A*Ap)
Bound = nE1 * nAp^2 + nE2 * nApA * nRightMP + nE4 * nLeftMP * nAp + (nE2 + nE4 * nAp * nE3) * nLeftMP * nRightMP
assert(oneNorm(F) <= Bound)
print "PASS: Moore-Penrose residual decomposition and 1-norm bound"

G = matrix {{1_QQ, 0}, {0, 0}}
Gg = G
Fg = matrix {{1/50_QQ, 1/80}, {-1/70, 1/60}}
Xg = Gg + Fg
I2 = id_(QQ^2)
P = Gg*G
D1 = Xg*G*Xg - Xg
D2 = Xg*G - G*Xg
D3 = G^2*Xg - G
RhsG = Gg*Gg*D3*P + (-Gg)*D2*(I2 - P) + (I2 - P)*D2*Gg + (I2 - P)*((-D2)*Gg*D2 - D1)*(I2 - P)
assertZero(Fg - RhsG, "group-inverse residual decomposition")
nGg = oneNorm Gg
nD1 = oneNorm D1
nD2 = oneNorm D2
nD3 = oneNorm D3
nComp = oneNorm(I2 - P)
BoundG = nGg^2 * nD3 + nGg * nD2 * nComp + nComp * nD2 * nGg + (nD1 + nD2^2 * nGg) * nComp^2
assert(oneNorm(Fg) <= BoundG)
print "PASS: group-inverse residual decomposition and 1-norm bound"

W = makeWA(QQ[x])
xW = W_0
Dx = W_1
assert(Dx*xW - xW*Dx == 1_W)
print "PASS: Dmodules Weyl commutator [Dx,x] = 1"

print "CAMPBELL1977_MACAULAY2_DMODULES_AUDIT_OK"
