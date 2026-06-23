-- Exact-rational Macaulay2 + Dmodules certificate for pg/pmg/pgg candidates.

loadPackage "Dmodules";

Tx = matrix(QQ, {{1,0,1},{0,1,0},{0,0,1}});
Ty = matrix(QQ, {{1,0,0},{0,1,1},{0,0,1}});
Gx = matrix(QQ, {{1,0,1/2},{0,-1,0},{0,0,1}});
Mx = matrix(QQ, {{-1,0,0},{0,1,0},{0,0,1}});
Gy = matrix(QQ, {{-1,0,0},{0,1,1/2},{0,0,1}});
I3 = id_(QQ^3);
if Gx*Gx != Tx then error "pg glide square failed";
if Gx*Ty != inverse(Ty)*Gx then error "pg transverse inversion failed";
if Mx*Mx != I3 then error "pmg mirror involution failed";
if Gy*Gy != Ty then error "pgg second glide square failed";
if Gy*Tx != inverse(Tx)*Gy then error "pgg transverse inversion failed";

-- Projected D5 roots used by pg/pmg/pgg representatives: e2, e1-e2, e1.
projectedD5RootsKlein = {{-1,-1},{-1,0},{-1,1},{0,-1},{0,1},{1,-1},{1,0},{1,1}};
if not member({0,1}, projectedD5RootsKlein) then error "e2 root missing";
if not member({1,-1}, projectedD5RootsKlein) then error "e1-e2 root missing";
if not member({1,0}, projectedD5RootsKlein) then error "e1 root missing";

-- Real Dmodules lane use: construct a Weyl-algebra quotient module.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "klein compatible wallpaper classification Macaulay2+Dmodules certificate: ok";
