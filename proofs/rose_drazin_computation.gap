# Exact-rational GAP witnesses for Rose's Drazin-inverse computation.

C1 := [[0,-1],[1,-5]];;
I2 := IdentityMat(2, Rationals);;
P1C := -24*C1 - 115*I2;;
if C1^3 * P1C <> I2 then Error("example 1 inverse-power matrix failed"); fi;

A1 := [[0,0,0,0],[0,0,0,0],[0,0,0,-1],[0,0,1,-5]];;
I4 := IdentityMat(4, Rationals);;
D1 := (A1^2) * (-24*A1 - 115*I4);;
if A1^3 * D1 <> A1^2 then Error("Drazin relation failed"); fi;
if D1 * A1 <> A1 * D1 then Error("commutation failed"); fi;

C2 := [[0,0,0,-1],[1,0,0,-1],[0,1,0,-1],[0,0,1,-1]];;
I4b := IdentityMat(4, Rationals);;
if C2 * C2^4 <> I4b then Error("example 2 inverse-power matrix failed"); fi;
Print("rose Drazin computation GAP certificate: ok\n");
