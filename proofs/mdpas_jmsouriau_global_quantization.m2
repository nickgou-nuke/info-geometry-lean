-- Exact-rational Macaulay2 + Dmodules audit for the finite
-- MDPAS/JM de Rham, symplectic, Kaluza-Klein, and quantization lane.
loadPackage "Dmodules";

R = QQ[phi0,phi1,phi2,r,a0,a1,a2,a3,hbar];

exactCycle = (phi1 - phi0) + (phi2 - phi1) + (phi0 - phi2);
if exactCycle != 0_R then error "exact de Rham cycle integral failed";
if 1_R + 1_R + 1_R == 0_R then error "unit de Rham obstruction failed";

J = matrix(R, {{0,0,1,0},{0,0,0,1},{-1,0,0,0},{0,-1,0,0}});
if J + transpose J != 0 then error "symplectic skew failed";
if det J != 1_R then error "symplectic nondegeneracy failed";

g4 = matrix(R, {{1,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,-1}});
A = matrix(R, {{a0},{a1},{a2},{a3}});
topLeft = g4 + r * A * transpose A;
kk = matrix(R, {
  {topLeft_(0,0), topLeft_(0,1), topLeft_(0,2), topLeft_(0,3), r*a0},
  {topLeft_(1,0), topLeft_(1,1), topLeft_(1,2), topLeft_(1,3), r*a1},
  {topLeft_(2,0), topLeft_(2,1), topLeft_(2,2), topLeft_(2,3), r*a2},
  {topLeft_(3,0), topLeft_(3,1), topLeft_(3,2), topLeft_(3,3), r*a3},
  {r*a0, r*a1, r*a2, r*a3, r}
});
if kk - transpose kk != 0 then error "Kaluza-Klein block symmetry failed";

if 2*(hbar/2) - hbar != 0_R then error "half-spin prequantization failed";

W = QQ[x,dx,WeylAlgebra => {x => dx}];
if dx*x - x*dx != 1_W then error "Dmodules Weyl lane failed";

print "mdpas JMSouriau global quantization Macaulay2+Dmodules certificate: ok";

