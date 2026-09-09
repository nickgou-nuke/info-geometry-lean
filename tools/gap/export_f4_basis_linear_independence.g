#! /usr/bin/env gap
#
# F4 basis linear-independence certificate exporter.
#
# Trust boundary:
#   Lean/Sage must first export the exact rational 52 x 52 coordinate matrix
#   of the 52 explicit derivations.  This GAP program checks that data only;
#   it does not identify arbitrary GAP matrices with Lean's f4Basis.
#
# Input protocol:
#   Read("f4_basis_matrix.g");
#   where f4BasisCoordinateMatrix is a list of 52 rows, each of length 52,
#   containing integers or rationals.
#   Then run this file with GAP.
#
# Output is a checked rank statement and a Lean-readable row certificate.

if not IsBound(f4BasisCoordinateMatrix) then
  Error("define f4BasisCoordinateMatrix before running the exporter");
fi;

M := f4BasisCoordinateMatrix;
if Length(M) <> 52 then
  Error("f4BasisCoordinateMatrix must have 52 rows");
fi;
if ForAny(M, r -> Length(r) <> 52) then
  Error("every row of f4BasisCoordinateMatrix must have length 52");
fi;

M := List(M, r -> List(r, Rat));
rank := RankMat(M);
if rank <> 52 then
  Error(Concatenation("coordinate matrix has rank ", String(rank),
    ", expected 52"));
fi;
determinant := DeterminantMat(M);
if determinant = 0 then
  Error("full-rank coordinate matrix has zero determinant");
fi;

Print("# INFO_GEOMETRY_F4_COORDINATE_CERTIFICATE v1\n");
Print("# carrier=H3Zorn_derivations\n");
Print("# basis_size=52\n");
Print("# coefficient_field=Rationals\n");
Print("# index_base=0\n");
Print("F4_BASIS_COORDINATE_MATRIX_ROWS=52\n");
Print("F4_BASIS_COORDINATE_MATRIX_COLS=52\n");
Print("F4_BASIS_COORDINATE_MATRIX_RANK=52\n");
Print("F4_BASIS_COORDINATE_MATRIX_DETERMINANT=", determinant, "\n");
Print("F4_BASIS_LINEAR_INDEPENDENCE_CERTIFICATE_BEGIN\n");
for i in [1..52] do
  Print("F4COORDROW ", i - 1, ": ", M[i], "\n");
od;
Print("F4_BASIS_LINEAR_INDEPENDENCE_CERTIFICATE_END\n");

# Emit a compact Lean datum.  The Lean owner must still prove that these
# rows are evaluations of the actual f4Basis derivations before consuming it.
Print("def f4BasisCoordinateMatrix : Matrix (Fin 52) (Fin 52) ℚ :=\n");
Print("  ![");
for i in [1..52] do
  if i > 1 then Print(",\n    "); fi;
  Print("![");
  for j in [1..52] do
    if j > 1 then Print(", "); fi;
    Print(String(M[i][j]));
  od;
  Print("]");
od;
Print("]\n");
