#!/usr/bin/env gap
# Exact certificate exporter for the 52 Lean F4 derivations acting on H3Zorn.
#
# The input matrix has 52 rows and 729 columns: each row is the flattened
# 27-by-27 action matrix of one actual Lean f4Basis element in a fixed
# H3Zorn coordinate basis.  This file never constructs or guesses that data.
# It only validates and serializes an explicitly supplied payload.

if not IsBound(f4BasisActionCoordinateMatrix) then
  Error("define f4BasisActionCoordinateMatrix before running the exporter");
fi;

# Keep machine-readable rows on one physical line for the translator.
SetPrintFormattingStatus("*stdout*", false);

M := f4BasisActionCoordinateMatrix;
if Length(M) <> 52 then
  Error("expected 52 derivation rows");
fi;
if ForAny(M, r -> Length(r) <> 729) then
  Error("expected 729 action coordinates per row (27 times 27)");
fi;

M := List(M, r -> List(r, Rat));
rank := RankMat(M);
if rank <> 52 then
  Error(Concatenation("action-coordinate matrix has rank ", String(rank),
    ", expected 52"));
fi;

# Compute a concrete column-pivot witness by row elimination.  RankMat alone
# is not exported as a proof: Lean must replay the selected minor.
extractPivots := function(A)
  local elimM, pivots, row, col, pivot, r, tmp, pivotValue, q;
  elimM := List(A, ShallowCopy);
  pivots := [];
  row := 1;
  for col in [1..729] do
    pivot := fail;
    for r in [row..52] do
      if elimM[r][col] <> 0 then
        pivot := r;
        break;
      fi;
    od;
    if pivot <> fail then
      tmp := elimM[row]; elimM[row] := elimM[pivot]; elimM[pivot] := tmp;
      pivotValue := elimM[row][col];
      elimM[row] := List(elimM[row], x -> x / pivotValue);
      for r in [row+1..52] do
        q := elimM[r][col];
        if q <> 0 then
          elimM[r] := List([1..729], c -> elimM[r][c] - q * elimM[row][c]);
        fi;
      od;
      Add(pivots, col);
      row := row + 1;
      if row = 53 then break; fi;
    fi;
  od;
  return pivots;
end;
pivots := extractPivots(M);
if Length(pivots) <> 52 then
  Error("pivot extraction failed to find 52 columns");
fi;
minor := List([1..52], i -> List(pivots, col -> M[i][col]));
minorDeterminant := Determinant(minor);

Print("# INFO_GEOMETRY_F4_ACTION_CERTIFICATE v1\n");
Print("# carrier=H3Zorn\n");
Print("# action_basis_dimension=27\n");
Print("# derivation_count=52\n");
Print("# flattened_action_coordinates=729\n");
Print("# coefficient_field=Rationals\n");
Print("# index_base=0\n");
Print("F4_ACTION_COORDINATE_ROWS=52\n");
Print("F4_ACTION_COORDINATE_COLS=729\n");
Print("F4_ACTION_COORDINATE_RANK=52\n");
Print("F4_ACTION_PIVOT_COUNT=52\n");
Print("F4_ACTION_MINOR_DETERMINANT=", minorDeterminant, "\n");
for i in [1..52] do
  Print("F4_ACTION_PIVOT ", i - 1, ": ", pivots[i] - 1, "\n");
od;
Print("F4_ACTION_MINOR_BEGIN\n");
for i in [1..52] do
  Print("F4_ACTION_MINOR_ROW ", i - 1, ": ",
    List(pivots, col -> M[i][col]), "\n");
od;
Print("F4_ACTION_MINOR_END\n");
Print("F4_ACTION_LINEAR_INDEPENDENCE_CERTIFICATE_BEGIN\n");
for i in [1..52] do
  Print("F4ACTIONROW ", i - 1, ": ", M[i], "\n");
od;
Print("F4_ACTION_LINEAR_INDEPENDENCE_CERTIFICATE_END\n");
QUIT_GAP(0);
