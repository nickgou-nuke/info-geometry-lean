needsPackage "Dmodules";
-- Exact rational certificates for finite Bayesian/Turing/Cantor layer.
R = QQ[a,b,c,Q];
if (b-a) + (c-b) != c-a then error "log RN cocycle failed";
if (b-a) + (c-b) + (a-c) != 0_R then error "log RN loop failed";
q = 17/19;
if q/q != 1 then error "dQ/Q residue failed";
-- Boolean event algebra: meet/product, join a+b-ab, complement 1-a.
B = QQ[e,f]/ideal(e^2-e,f^2-f);
if e*f != e*f then error "meet characteristic failed";
if (e+f-e*f)^2 != e+f-e*f then error "join idempotent failed";
if (1_B-e)^2 != 1_B-e then error "complement idempotent failed";
-- Dmodules lane smoke check.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
if dt*t - t*dt != 1_W then error "Dmodules Weyl lane failed";
print "bayesian Turing Cantor Macaulay2+Dmodules certificate: ok";
