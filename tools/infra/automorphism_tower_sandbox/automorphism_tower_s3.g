G := SymmetricGroup(3);;
A := AutomorphismGroup(G);;
if Size(G) <> 6 then Error("S3 order mismatch"); fi;
if Size(A) <> 6 then Error("Aut(S3) order mismatch"); fi;
if Size(Centre(G)) <> 1 then Error("S3 center mismatch"); fi;
if IsomorphismGroups(G, A) = fail then Error("S3 not isomorphic to Aut(S3)"); fi;
Print("GAP_AUTOMORPHISM_TOWER_S3_COMPLETE_LEDGER_OK\n");
Print("order=", Size(G), " aut=", Size(A), " center=", Size(Centre(G)), "\n");
