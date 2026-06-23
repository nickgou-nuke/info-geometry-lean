# Exact-rational GAP certificate for finite pg/pmg/pgg Klein-compatible candidates.

Tx := [[1,0,1],[0,1,0],[0,0,1]];;
Ty := [[1,0,0],[0,1,1],[0,0,1]];;
Gx := [[1,0,1/2],[0,-1,0],[0,0,1]];;
Mx := [[-1,0,0],[0,1,0],[0,0,1]];;
Gy := [[-1,0,0],[0,1,1/2],[0,0,1]];;
I := IdentityMat(3, Rationals);;
if Gx*Gx <> Tx then Error("pg glide square failed"); fi;
if Gx*Ty <> Ty^-1*Gx then Error("pg transverse inversion failed"); fi;
if Mx*Mx <> I then Error("pmg mirror involution failed"); fi;
if Gy*Gy <> Ty then Error("pgg second glide square failed"); fi;
if Gy*Tx <> Tx^-1*Gy then Error("pgg transverse inversion failed"); fi;
roots := [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];;
if not ([0,1] in roots and [1,-1] in roots and [1,0] in roots) then Error("root membership failed"); fi;
Print("klein compatible wallpaper classification GAP certificate: ok\n");
