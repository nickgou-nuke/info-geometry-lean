W := DihedralGroup(IsPermGroup, 12);;
if Size(W) <> 12 then Error("G2 Weyl order mismatch"); fi;
if Length(GeneratorsOfGroup(W)) < 2 then Error("expected dihedral generators"); fi;
Print("GAP_REAL_SPLIT_G2_WEYL_OK order ", Size(W), "\n");
QUIT;
