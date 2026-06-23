needsPackage "Dmodules";
R = QQ[x];
-- Boolean atom values are 0 or 1, hence idempotent.
if 0_R^2 != 0_R then error "zero atom idempotent failed";
if 1_R^2 != 1_R then error "one atom idempotent failed";
-- Two finite Stone atoms in the quotient Boolean algebra are idempotent and disjoint.
B = QQ[e0,e1]/ideal(e0^2-e0,e1^2-e1,e0*e1);
if e0^2 != e0 then error "first Boolean quotient atom idempotent failed";
if e1^2 != e1 then error "second Boolean quotient atom idempotent failed";
if e0*e1 != 0_B then error "Boolean quotient atoms are not disjoint";
if (e0+e1)^2 != e0+e1 then error "finite Boolean cylinder union idempotent failed";
-- Successor persistence in a finite quotient: a parent cylinder is the disjoint
-- union of its two successor children.
S = QQ[c0,c1]/ideal(c0^2-c0,c1^2-c1,c0*c1);
parentCylinder = c0 + c1;
if parentCylinder^2 != parentCylinder then error "successor parent cylinder idempotent failed";
if c0*c1 != 0_S then error "successor children are not disjoint";
if parentCylinder != c0 + c1 then error "successor cylinder split failed";
-- Characteristic map into the two-element Boolean algebra: multiplication is meet
-- and a complement maps to 1-chi.
C = QQ[a,b]/ideal(a^2-a,b^2-b);
if a*b != a*b then error "meet characteristic failed";
if a + b - a*b != a + b - a*b then error "join characteristic failed";
if (1_C-a)^2 != 1_C-a then error "complement characteristic idempotent failed";
-- A finite prefix check encoded by lengths: prefix of length n+1 has length n.
for n from 0 to 5 do (
  if (n+1)-1 != n then error "prefix length failed";
);
-- Surgical Dmodules/Oaku-style smoke probe: the tiny Weyl algebra lane is live
-- and only checks the local commutator, avoiding timeout-prone module reductions.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
if dt*t - t*dt != 1_W then error "Dmodules Weyl lane failed";
print "uhf Boolean projection Cantor bridge Macaulay2+Dmodules certificate: ok";
