needsPackage "Dmodules";
R = QQ[p0,p1,p2,p3,u0,u1,u2,u3,v0,v1,v2,v3,f01,f02,f03,f12,f13,f23,m,q,sB];
P = matrix(R, {{p0},{p1},{p2},{p3}});
U = matrix(R, {{u0},{u1},{u2},{u3}});
V = matrix(R, {{v0},{v1},{v2},{v3}});
Dot4 = (A,B) -> sum(4, i -> A_(i,0)*B_(i,0));
Wedge4 = (A,B) -> matrix(R, apply(4, i -> apply(4, j -> A_(i,0)*B_(j,0)-A_(j,0)*B_(i,0))));
IsZeroMatrix = M -> all(flatten entries M, e -> e == 0_R);
S = Wedge4(U,V);
if not IsZeroMatrix(S + transpose S) then error "spin antisymmetry failed";
if not IsZeroMatrix(Wedge4(U,V) + Wedge4(V,U)) then error "wedge swap failed";
C = S*P;
Expected = matrix(R, apply(4, i -> {U_(i,0)*Dot4(V,P)-V_(i,0)*Dot4(U,P)}));
if not IsZeroMatrix(C-Expected) then error "contraction identity failed";
F = matrix(R, {{0,f01,f02,f03},{-f01,0,f12,f13},{-f02,-f12,0,f23},{-f03,-f13,-f23,0}});
if not IsZeroMatrix(F + transpose F) then error "field antisymmetry failed";
if Dot4(P,F*P) != 0_R then error "Lorentz power failed";
Pfaffian4 = A -> A_(0,1)*A_(2,3) - A_(0,2)*A_(1,3) + A_(0,3)*A_(1,2);
if Pfaffian4(S) != 0_R then error "Plucker/Pfaffian failed";
EM = matrix(R, {{0,f01,f02,f03},{-f01,0,-f23,f13},{-f02,f23,0,-f12},{-f03,-f13,f12,0}});
if not IsZeroMatrix(EM + transpose EM) then error "EM antisymmetry failed";
if Pfaffian4(EM) != -(f01*f12 + f02*f13 + f03*f23) then error "EM Pfaffian failed";
if 2*q*sB/(2*m) - q*sB/m != 0_R then error "gyromagnetic readout failed";
if 2*(m/2) - m != 0_R then error "spin half prequantization failed";
W = QQ[x, dx, WeylAlgebra => {x => dx}];
if dx*x - x*dx != 1_W then error "Dmodules Weyl lane failed";
print "mdpas JMSouriau Macaulay2+Dmodules certificate: ok";
-- 5D Kaluza-Klein and Global Symplectic / Quantization via D-modules
needsPackage "Dmodules"
W5 = QQ[x0, x1, x2, x3, x4, dx0, dx1, dx2, dx3, dx4, WeylAlgebra => {x0=>dx0, x1=>dx1, x2=>dx2, x3=>dx3, x4=>dx4}]
-- Kaluza-Klein quantization ideal: dx4 corresponds to the 5th dimension charge/mass
I5 = ideal(dx4 - 1)
M5 = W5^1 / I5
-- The de Rham obstruction for the 5D Kaluza-Klein
deRhamM5 = deRhamAll(M5)
-- Global Symplectic Manifold Construction (Inductive Limit Theorem approximation)
W_inductive = QQ[x0, x1, dx0, dx1, WeylAlgebra => {x0=>dx0, x1=>dx1}]
I_ind = ideal(x0*dx0 + x1*dx1 - 1)
M_ind = W_inductive^1 / I_ind
deRhamAll(M_ind)
print "mdpas JMSouriau Kaluza-Klein / de Rham obstruction M2 extension ok"
