needsPackage "Dmodules";

R = QQ[p];
S = R/ideal(p^2 - p - 1);
phi = substitute(p, S);

inv2 = 2 - phi;
inv3 = 2*phi - 3;
inv5 = 5*phi - 8;
expr = 360*inv2 - 2*inv3 + inv5/243;
goalForm = 176410/243 - (88447/243)*phi;

print "MACAULAY2 / DMODULES PASS";
print concatenate("normal_form_remainder = ", toString(expr - goalForm));

W = QQ[x, Dx, WeylAlgebra => {x => Dx}];
use W;
print concatenate("weyl_ring_dim = ", toString dim W);
print concatenate("weyl_sample_relation = ", toString(Dx*x - x*Dx));
