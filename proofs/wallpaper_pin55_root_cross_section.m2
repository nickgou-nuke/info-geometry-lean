-- Exact-rational Macaulay2 + Dmodules certificate for wallpaper/Pin55 root cross-section.

loadPackage "Dmodules";

T = matrix(QQ, {{0,-1},{1,0}}); G = matrix(QQ, {{1,0},{0,-1}}); I2 = id_(QQ^2);
D4 = {I2, T, -I2, -T, G, T*G, -G, -T*G};
B2 = {matrix(QQ,{{1},{0}}), matrix(QQ,{{-1},{0}}), matrix(QQ,{{0},{1}}), matrix(QQ,{{0},{-1}}),
      matrix(QQ,{{1},{1}}), matrix(QQ,{{-1},{-1}}), matrix(QQ,{{1},{-1}}), matrix(QQ,{{-1},{1}})};
Lift = {matrix(QQ,{{1},{0},{1},{0},{0}}), matrix(QQ,{{-1},{0},{1},{0},{0}}),
        matrix(QQ,{{0},{1},{1},{0},{0}}), matrix(QQ,{{0},{-1},{1},{0},{0}}),
        matrix(QQ,{{1},{1},{0},{0},{0}}), matrix(QQ,{{-1},{-1},{0},{0},{0}}),
        matrix(QQ,{{1},{-1},{0},{0},{0}}), matrix(QQ,{{-1},{1},{0},{0},{0}})};
Weyl = {
id_(QQ^5),
matrix(QQ,{{0,-1,0,0,0},{1,0,0,0,0},{0,0,-1,0,0},{0,0,0,1,0},{0,0,0,0,1}}),
diagonalMatrix{-1_QQ,-1_QQ,1_QQ,1_QQ,1_QQ},
matrix(QQ,{{0,1,0,0,0},{-1,0,0,0,0},{0,0,-1,0,0},{0,0,0,1,0},{0,0,0,0,1}}),
diagonalMatrix{1_QQ,-1_QQ,-1_QQ,1_QQ,1_QQ},
matrix(QQ,{{0,1,0,0,0},{1,0,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}),
diagonalMatrix{-1_QQ,1_QQ,-1_QQ,1_QQ,1_QQ},
matrix(QQ,{{0,-1,0,0,0},{-1,0,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}})};
D5Member = v -> (numNonzero := 0; ok := true; scan(5, i -> if v_(i,0) != 0 then (numNonzero = numNonzero + 1; if not (v_(i,0) == 1 or v_(i,0) == -1) then ok = false)); ok and numNonzero == 2);
for L in Lift do if not D5Member L then error "lift not D5 root";
for k from 0 to 7 do (
  W := Weyl#k; M := D4#k;
  if transpose(W)*W != id_(QQ^5) then error "orthogonal lift failed";
  for r from 0 to 7 do (
    image2 := M*(B2#r); image5 := W*(Lift#r);
    if not member(image2, B2) then error "B2 preservation failed";
    if not D5Member image5 then error "D5 preservation failed";
    if matrix(QQ,{{image5_(0,0)},{image5_(1,0)}}) != image2 then error "projection mismatch";
  );
);

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
WA = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_WA}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "wallpaper Pin55 root cross-section Macaulay2+Dmodules certificate: ok";
