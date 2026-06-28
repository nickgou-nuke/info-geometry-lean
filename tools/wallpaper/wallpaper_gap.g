id3 := IdentityMat(3, Rationals);;
tx := [[1,0,1],[0,1,0],[0,0,1]];;
ty := [[1,0,0],[0,1,1],[0,0,1]];;
r2 := [[-1,0,0],[0,-1,0],[0,0,1]];;
mx := [[1,0,0],[0,-1,0],[0,0,1]];;
gx := [[1,0,1/2],[0,-1,0],[0,0,1]];;

txInv := [[1,0,-1],[0,1,0],[0,0,1]];;
tyInv := [[1,0,0],[0,1,-1],[0,0,1]];;

if r2 * r2 <> id3 then Error("p2 square failed"); fi;
if r2 * tx * r2 <> txInv then Error("p2 conjugation failed"); fi;
if mx * mx <> id3 then Error("pm square failed"); fi;
if mx * ty * mx <> tyInv then Error("pm conjugation failed"); fi;
if gx * gx <> tx then Error("pg square failed"); fi;
if gx * ty * gx^-1 <> tyInv then Error("pg conjugation failed"); fi;

Print("WALLPAPER_GAP_OK\n");
QUIT;
