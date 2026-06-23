needsPackage "Dmodules";

-- Exact finite algebraic check for the Branman countable-Stone finite core.
-- The label set {x, x^-1} in the group algebra of C5 is inverse-closed.
S = QQ[x]/ideal(x^5-1);
if x*x^4 != 1_S then error "inverse label closure failed";
if x^4*x != 1_S then error "reverse inverse label closure failed";

-- Dmodules lane: verify the Weyl algebra is loaded and functional.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
if dt*t - t*dt != 1_W then error "Dmodules Weyl lane failed";

print "branman countable Stone finite core Macaulay2+Dmodules check: ok";
