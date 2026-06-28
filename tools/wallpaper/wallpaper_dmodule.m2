loadPackage "Dmodules";

TX = matrix(QQ, {{1,0,1},{0,1,0},{0,0,1}});
TY = matrix(QQ, {{1,0,0},{0,1,1},{0,0,1}});
R2 = matrix(QQ, {{-1,0,0},{0,-1,0},{0,0,1}});
MX = matrix(QQ, {{1,0,0},{0,-1,0},{0,0,1}});
GX = matrix(QQ, {{1,0,1/2},{0,-1,0},{0,0,1}});
I3 = id_(QQ^3);

if R2*R2 != I3 then error "p2 square failed";
if R2*TX*R2 != matrix(QQ, {{1,0,-1},{0,1,0},{0,0,1}}) then error "p2 conjugation failed";
if MX*MX != I3 then error "pm square failed";
if MX*TY*MX != matrix(QQ, {{1,0,0},{0,1,-1},{0,0,1}}) then error "pm conjugation failed";
if GX*GX != TX then error "pg square failed";
if GX*TY*inverse GX != matrix(QQ, {{1,0,0},{0,1,-1},{0,0,1}}) then error "pg conjugation failed";

W = QQ[t, dt, WeylAlgebra => {t => dt}];
N = cokernel matrix{{t*dt - dt*t - 1_W}};
if numgens source presentation N != 1 then error "Dmodule sanity failed";

print "WALLPAPER_M2_OK";
