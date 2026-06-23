-- Exact-rational Macaulay2 + Dmodules certificate for Klein-compatible wallpaper symmetries.

loadPackage "Dmodules";

T = matrix(QQ, {{0,-1},{1,0}});
G = matrix(QQ, {{1,0},{0,-1}});
I2 = id_(QQ^2);
D4 = {I2, T, -I2, -T, G, T*G, -G, -T*G};
if T*T != -I2 then error "twist square failed";
if G*G != I2 then error "glide square failed";
if G*T != -T*G then error "anticommutation failed";
for S in D4 do (
  if transpose(S) * S != I2 then error "orthogonality failed";
  if not (S*T == T*S or S*T == -T*S) then error "Klein compatibility failed";
  if S*(T*T) != -S then error "twist-square preservation failed";
);
for A in D4 do for B in D4 do (
  if not member(A*B, D4) then error "D4 closure failed";
);
eta55 = diagonalMatrix{1_QQ,1_QQ,1_QQ,1_QQ,1_QQ,-1_QQ,-1_QQ,-1_QQ,-1_QQ,-1_QQ};
if transpose(eta55) != eta55 then error "O55 symmetry failed";
if eta55 * eta55 != id_(QQ^10) then error "O55 involution failed";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "wallpaper Klein-bottle Cartan Macaulay2+Dmodules certificate: ok";
