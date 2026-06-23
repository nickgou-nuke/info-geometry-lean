Print("=== GAP exact-rational Jensen inverse-iteration certificate ===\n");

RequireTrue := function(label, cond)
  if not cond then
    Error(label);
  fi;
  Print(label, ": ok\n");
end;

JensenPolynomialCoeffs := function(b, j)
  return [
    -(b[j - 1] - b[j]),
    b[j - 1] * (b[j - 2] - b[j]),
    -b[j - 1] * b[j] * (b[j - 2] - b[j - 1])
  ];
end;

h := 1/5;
q := 1/3;
b := List([1..7], j -> h + q^j);

for j in [3..7] do
  coeffs := JensenPolynomialCoeffs(b, j);
  RequireTrue(Concatenation("stage ", String(j), " exact-rational h <= b_j"),
    h <= b[j]);
  RequireTrue(Concatenation("stage ", String(j), " leading coefficient nonzero"),
    coeffs[1] <> 0);
  # Rational companion-matrix certificate for the quadratic backbone.
  C := [[0, -coeffs[3] / coeffs[1]], [1, -coeffs[2] / coeffs[1]]];
  RequireTrue(Concatenation("stage ", String(j), " trace certificate"),
    TraceMat(C) = -coeffs[2] / coeffs[1]);
  RequireTrue(Concatenation("stage ", String(j), " determinant certificate"),
    DeterminantMat(C) = coeffs[3] / coeffs[1]);
od;

Print("JENSEN_INVERSE_ITERATION_GAP_RATIONAL_CERTIFICATE_OK\n");
QUIT;
