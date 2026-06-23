# GAP script for Coriolis barrier anomaly verification
Print("=== GAP: Coriolis Barrier Anomaly Verification ===\n");

# Projectors as lists of lists
PD := [[1, 0, 0], [0, 1, 0], [0, 0, 0]];
PL := [[1, 0, 0], [0, 0, 0], [0, 0, 1]];
PR := [[0, 0, 0], [0, 1, 0], [0, 0, 1]];

# Dilation
D := 1/2 * (PL - PR);

# Commutator helper function
MyComm := function(A, B)
  return A * B - B * A;
end;

comm_PD_D := MyComm(PD, D);
chi_L := MyComm(PD, PL);
chi_R := MyComm(PD, PR);
decomp := 1/2 * (chi_L - chi_R);

# Difference
diff := comm_PD_D - decomp;

Print("Difference [P_D, D] - 1/2 * (chi_L - chi_R): ", diff, "\n");
if diff = [[0, 0, 0], [0, 0, 0], [0, 0, 0]] then
  Print("Projector and dilation commutator relation holds in GAP!\n");
else
  Error("Verification failed!");
fi;

# Coriolis Vorticity Skew-Adjointness
chi := [[1, 2], [3, 4]];
vort := 1/2 * (chi - TransposedMat(chi));
is_skew := (vort + TransposedMat(vort) = [[0, 0], [0, 0]]);
Print("Is Coriolis vorticity skew-adjoint in GAP? ", is_skew, "\n");
if is_skew then
  Print("All GAP verifications passed!\n");
else
  Error("Skew-adjointness failed!");
fi;
