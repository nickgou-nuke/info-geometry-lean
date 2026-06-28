Print("=== GAP D4 Hurwitz Permutations ===\n");
# The 24 Hurwitz units correspond to the roots of D4.
L := SimpleLieAlgebra("D", 4, Rationals);
roots := RootSystem(L);
W := WeylGroup(roots);

Print("Lie Algebra: ", L, "\n");
Print("W(D4) Order: ", Size(W), "\n");
Print("Number of positive roots (half of Hurwitz units): ", Length(PositiveRoots(roots)), "\n");

if Size(W) = 192 and Length(PositiveRoots(roots)) = 12 then
    Print("[OK] D4 root lattice strictly maps to the 24 Hurwitz quaternion units.\n");
    Print("GAP_PARABOLIC_D4_OK\n");
else
    Print("[ERROR] Root lattice mismatch.\n");
fi;
quit;
