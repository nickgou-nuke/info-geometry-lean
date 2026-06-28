# tools/gap/tkk_d4.g
# Simple test for D4 in GAP

L := SimpleLieAlgebra("D", 4, Rationals);
Print("Lie algebra D4 over Rationals: ", L, "\n");
Print("Dimension: ", Dimension(L), "\n");
# Try to compute the Chevalley basis
C := ChevalleyBasis(L);
Print("Chevalley basis computed.\n");
# Simple root system
R := RootSystem(L);
Print("Root system: ", R, "\n");
Print("Success.\n");
quit;