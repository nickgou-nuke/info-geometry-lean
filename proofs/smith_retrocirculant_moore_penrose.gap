# Exact-rational GAP witnesses for Smith's retrocirculant Moore--Penrose inverse.

A := [[0,3],[2,0]];;
Ap := [[0,1/2],[1/3,0]];;
if A * Ap * A <> A then Error("ABA=A failed"); fi;
if Ap * A * Ap <> Ap then Error("BAB=B failed"); fi;
if TransposedMat(A * Ap) <> A * Ap then Error("AB symmetry failed"); fi;
if TransposedMat(Ap * A) <> Ap * A then Error("BA symmetry failed"); fi;
B := [[0,7],[5,0]];;
prod := A * B;;
if prod[1][2] <> 0 or prod[2][1] <> 0 then Error("product circulant/diagonal check failed"); fi;
Print("smith retrocirculant Moore-Penrose GAP certificate: ok\n");
