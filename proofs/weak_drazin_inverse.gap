# Exact-rational GAP certificate for Campbell--Meyer weak Drazin inverses.

A := [[2,0,0],[0,0,1],[0,0,0]];;
Bmin := [[1/2,0,0],[0,0,0],[0,0,0]];;
Bpoly := [[1/2,0,0],[0,1/2,0],[0,0,1/2]];;
k := 2;;
if Bmin * (A ^ (k+1)) <> A ^ k then Error("minimal weak Drazin check failed"); fi;
if Bpoly * (A ^ (k+1)) <> A ^ k then Error("polynomial weak Drazin check failed"); fi;
if A * Bpoly <> Bpoly * A then Error("commuting check failed"); fi;
Print("weak Drazin GAP certificate: ok\n");
