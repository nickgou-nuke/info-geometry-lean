LoadPackage("liealgdb");
L := SimpleLieAlgebra("F", 4, Rationals);
B := Basis(L);
T := StructureConstantsTable(B);
dim := Dimension(L);

Print("def f4_c (i j k : Fin 52) : ℝ :=\n");
Print("  match i.val, j.val, k.val with\n");

for i in [1..dim] do
  for j in [1..dim] do
    # T[i][j] is a list of [coefficient, basis_index, coefficient, basis_index, ...] in some versions,
    # or a list of length `dim` of coefficients in others?
    # In GAP, StructureConstantsTable returns a table.
    # A better way is:
    v := B[i] * B[j];
    coeffs := Coefficients(B, v);
    for k in [1..dim] do
      if coeffs[k] <> 0 then
        Print("  | ", i-1, ", ", j-1, ", ", k-1, " => ", coeffs[k], "\n");
      fi;
    od;
  od;
od;
Print("  | _, _, _ => 0\n");
QUIT_GAP(0);
