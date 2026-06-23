# GAP exact witness for trace-free scaling of Lie Algebra generators.

RequireTrue := function(label, cond)
  if not cond then Error(Concatenation(label, " failed")); fi;
  Print("  ✅ ", label, "\n");
end;

Print("============================================================\n");
Print("GAP EVIDENCE: LIE ALGEBRA TRACE-FREE SCALING\n");
Print("============================================================\n");

# 1. Trace function
Trace2x2 := function(mat)
  return mat[1][1] + mat[2][2];
end;

# 2. Define a trace-free generator K (representing the modular Hamiltonian)
K := [[1, 2], [3, -1]];
RequireTrue("Trace of K is 0", Trace2x2(K) = 0);

# 3. Test trace-free scaling under arbitrary scalar beta
beta_vals := [-5, 0, 1, 3, 10];
for b in beta_vals do
  scaled_K := b * K;
  RequireTrue(Concatenation("Trace of scaled ", String(b), " * K remains 0"), Trace2x2(scaled_K) = 0);
od;

# 4. Zero product trace scaling check: Tr(beta * K) = 0 iff beta = 0 or Tr(K) = 0
K2 := [[1, 2], [3, 4]];
RequireTrue("Trace of K2 is non-zero", Trace2x2(K2) <> 0);
RequireTrue("Trace of 0 * K2 is 0", Trace2x2(0 * K2) = 0);
RequireTrue("Trace of 3 * K2 is non-zero", Trace2x2(3 * K2) <> 0);

Print("============================================================\n");
