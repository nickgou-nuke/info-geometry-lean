Print("Geometric Langlands / Automorphic Galois Representations: Finite Invariant Groups\n");
Print("=================================================================================\n");

Print("1. Finite subgroups of PGL(2, C) (Tetrahedral, Octahedral, Icosahedral)\n");
A4 := AlternatingGroup(4);
S4 := SymmetricGroup(4);
A5 := AlternatingGroup(5);

Print("Tetrahedral group (A4): ", StructureDescription(A4), " Order: ", Order(A4), "\n");
Print("Octahedral group (S4): ", StructureDescription(S4), " Order: ", Order(S4), "\n");
Print("Icosahedral group (A5): ", StructureDescription(A5), " Order: ", Order(A5), "\n");

Print("\n2. GL(2, F_p) representations\n");
GL23 := GL(2, 3);
PGL23 := PGL(2, 3);
SL23 := SL(2, 3);
PSL23 := PSL(2, 3);

Print("GL(2, 3): ", StructureDescription(GL23), " Order: ", Order(GL23), "\n");
Print("PGL(2, 3): ", StructureDescription(PGL23), " Order: ", Order(PGL23), "\n");
Print("SL(2, 3): ", StructureDescription(SL23), " Order: ", Order(SL23), "\n");
Print("PSL(2, 3): ", StructureDescription(PSL23), " Order: ", Order(PSL23), "\n");

Print("\n3. Derived subgroups and character degrees\n");
Print("Derived subgroup of GL(2, 3): ", StructureDescription(DerivedSubgroup(GL23)), "\n");

Print("\nComputing Character Degrees:\n");
Print("Degrees for A4: ", CharacterDegrees(A4), "\n");
Print("Degrees for S4: ", CharacterDegrees(S4), "\n");
Print("Degrees for A5: ", CharacterDegrees(A5), "\n");
Print("Degrees for GL(2, 3): ", CharacterDegrees(GL23), "\n");
Print("Degrees for SL(2, 3): ", CharacterDegrees(SL23), "\n");

Print("\nDone.\n");
QUIT;
