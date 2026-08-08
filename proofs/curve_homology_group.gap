# curve_homology_group.gap
# H_1(R^2 \ {0}) is isomorphic to Z
# We represent this as a finitely presented group with one generator (the loop around the puncture).
F := FreeGroup("a");
# No relators, since it's the free group of rank 1
H1 := F / [];
Print("H_1(R^2 \\ {0}) is isomorphic to: ", StructureDescription(H1), "\n");
Print("The generator 'a' represents a curve with winding number 1.\n");
a := H1.1;
Print("An element like 'a^3' represents a curve with winding number 3: ", a^3, "\n");
