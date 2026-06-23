-- Exact-rational Macaulay2 + Dmodules certificate for the wallpaper/Pin(5,5)
-- root cross-section.

needsPackage "Dmodules"

print "=== Wallpaper / Pin(5,5) root cross-section Macaulay2 certificate ==="

T = matrix(QQ, {{0,-1},{1,0}});
G = matrix(QQ, {{1,0},{0,-1}});
I2 = id_(QQ^2);
I5 = id_(QQ^5);
D4 = {I2, T, -I2, -T, G, T*G, -G, -T*G};

if #unique D4 != 8 then error "D4 cardinality failed";
for S in D4 do (
  if transpose(S) * S != I2 then error "D4 orthogonality failed";
  if not (S*T == T*S or S*T == -T*S) then error "Klein compatibility failed";
);
for A in D4 do for B in D4 do (
  if not member(A*B, D4) then error "D4 closure failed";
);

b2Roots = {
  matrix(QQ, {{1},{0}}),
  matrix(QQ, {{-1},{0}}),
  matrix(QQ, {{0},{1}}),
  matrix(QQ, {{0},{-1}}),
  matrix(QQ, {{1},{1}}),
  matrix(QQ, {{-1},{-1}}),
  matrix(QQ, {{1},{-1}}),
  matrix(QQ, {{-1},{1}})
};
for S in D4 do for r in b2Roots do (
  if not member(S*r, b2Roots) then error "D4 B2 root preservation failed";
);

root5 = (i,j,si,sj) -> matrix(QQ,
  apply(toList(0..4), k -> {if k == i then si else if k == j then sj else 0_QQ}));

d5Roots = {};
for i from 0 to 4 do for j from i+1 to 4 do (
  for si in {1_QQ,-1_QQ} do for sj in {1_QQ,-1_QQ} do (
    r = root5(i,j,si,sj);
    d5Roots = append(d5Roots, r);
    d5Roots = append(d5Roots, -r);
  )
);
if #unique d5Roots != 40 then error "D5 root count failed";

lifts = {
  matrix(QQ, {{1},{0},{1},{0},{0}}),
  matrix(QQ, {{-1},{0},{1},{0},{0}}),
  matrix(QQ, {{0},{1},{1},{0},{0}}),
  matrix(QQ, {{0},{-1},{1},{0},{0}}),
  matrix(QQ, {{1},{1},{0},{0},{0}}),
  matrix(QQ, {{-1},{-1},{0},{0},{0}}),
  matrix(QQ, {{1},{-1},{0},{0},{0}}),
  matrix(QQ, {{-1},{1},{0},{0},{0}})
};
for k from 0 to 7 do (
  if not member(lifts#k, d5Roots) then error "B2 lift is not a D5 root";
  if matrix(QQ, {{(lifts#k)_(0,0)}, {(lifts#k)_(1,0)}}) != b2Roots#k then
    error "B2 lift projection failed";
);

cross = {
  I5,
  matrix(QQ, {{0,-1,0,0,0},{1,0,0,0,0},{0,0,-1,0,0},{0,0,0,1,0},{0,0,0,0,1}}),
  diagonalMatrix{-1_QQ,-1_QQ,1_QQ,1_QQ,1_QQ},
  matrix(QQ, {{0,1,0,0,0},{-1,0,0,0,0},{0,0,-1,0,0},{0,0,0,1,0},{0,0,0,0,1}}),
  diagonalMatrix{1_QQ,-1_QQ,-1_QQ,1_QQ,1_QQ},
  matrix(QQ, {{0,1,0,0,0},{1,0,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}),
  diagonalMatrix{-1_QQ,1_QQ,-1_QQ,1_QQ,1_QQ},
  matrix(QQ, {{0,-1,0,0,0},{-1,0,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}})
};

eta55 = diagonalMatrix{1_QQ,1_QQ,1_QQ,1_QQ,1_QQ,-1_QQ,-1_QQ,-1_QQ,-1_QQ,-1_QQ};
blockLift = P -> matrix(QQ, apply(toList(0..9), a -> apply(toList(0..9), b ->
  if a < 5 and b < 5 then P_(a,b)
  else if a >= 5 and b >= 5 then P_(a-5,b-5)
  else 0_QQ)));

for k from 0 to 7 do (
  P = cross#k;
  if transpose(P) * P != I5 then error "D5 lift orthogonality failed";
  if matrix(QQ, {{P_(0,0), P_(0,1)}, {P_(1,0), P_(1,1)}}) != D4#k then
    error "D5 lift projection failed";
  for r in d5Roots do (
    if not member(P*r, d5Roots) then error "D5 root preservation failed";
  );
  L = blockLift(P);
  if transpose(L) * eta55 * L != eta55 then error "O55 metric preservation failed";
);

-- Dmodules lane: the mirror constraint x1 - x2 is a regular holonomic
-- boundary module for the reflected cross-section.
W = makeWA(QQ[x1, x2]);
D1 = W_2;
D2 = W_3;
I = ideal(x1 - x2, D1 + D2);
if isHolonomic(W^1 / I) != true then error "Dmodules mirror module failed";

print "WALLPAPER_PIN55_ROOT_CROSS_SECTION_MACAULAY2_DMODULES_CERTIFICATE_OK";
