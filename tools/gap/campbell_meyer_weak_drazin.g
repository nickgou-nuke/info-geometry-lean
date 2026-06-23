Print("=== GAP Campbell--Meyer 1978 weak Drazin certificate ===\n");

ZeroMatLocal := function(rows, cols)
  return List([1..rows], i -> List([1..cols], j -> 0));
end;

DeltaLocal := function(i, j)
  if i = j then
    return 1;
  fi;
  return 0;
end;

IdentityMatLocal := function(n)
  return List([1..n], i -> List([1..n], j -> DeltaLocal(i, j)));
end;

MatMulLocal := function(A, B)
  local rows, mids, cols;
  rows := Length(A);
  mids := Length(B);
  cols := Length(B[1]);
  return List([1..rows], i ->
    List([1..cols], j -> Sum([1..mids], k -> A[i][k] * B[k][j])));
end;

MatSubLocal := function(A, B)
  return List([1..Length(A)], i ->
    List([1..Length(A[1])], j -> A[i][j] - B[i][j]));
end;

MatPowLocal := function(A, n)
  local result, i;
  result := IdentityMatLocal(Length(A));
  for i in [1..n] do
    result := MatMulLocal(result, A);
  od;
  return result;
end;

ScalarMulMatLocal := function(q, A)
  return List(A, row -> List(row, x -> q * x));
end;

AssertZeroMatLocal := function(M, label)
  if M <> ZeroMatLocal(Length(M), Length(M[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

AssertWeakLocal := function(A, B, k, label)
  AssertZeroMatLocal(MatSubLocal(MatMulLocal(B, MatPowLocal(A, k + 1)), MatPowLocal(A, k)),
    Concatenation(label, ": B A^(k+1) = A^k"));
end;

AssertDrazinLocal := function(A, D, k, label)
  AssertZeroMatLocal(MatSubLocal(MatMulLocal(A, D), MatMulLocal(D, A)),
    Concatenation(label, ": A D = D A"));
  AssertZeroMatLocal(MatSubLocal(MatMulLocal(MatMulLocal(D, A), D), D),
    Concatenation(label, ": D A D = D"));
  AssertZeroMatLocal(MatSubLocal(MatMulLocal(MatPowLocal(A, k + 1), D), MatPowLocal(A, k)),
    Concatenation(label, ": A^(k+1)D = A^k"));
end;

A := [[2,0,0],[0,0,1],[0,0,0]];
Nil := [[0,0,0],[0,0,1],[0,0,0]];
I3 := IdentityMatLocal(3);

if MatPowLocal(Nil, 2) <> ZeroMatLocal(3, 3) then Error("nilpotent lane failed"); fi;
if MatPowLocal(A, 3) <> ScalarMulMatLocal(2, MatPowLocal(A, 2)) then Error("polynomial failed"); fi;

D := [[1/2,0,0],[0,0,0],[0,0,0]];
AssertDrazinLocal(A, D, 2, "Drazin inverse");
AssertWeakLocal(A, D, 2, "Drazin inverse");

Wild := [[1/2,3,5],[0,7,11],[0,13,17]];
AssertWeakLocal(A, Wild, 2, "wild weak inverse");
if Wild = D then Error("weak inverse should be nonunique"); fi;
if MatMulLocal(A, Wild) = MatMulLocal(Wild, A) then Error("wild inverse should not commute"); fi;

Poly := ScalarMulMatLocal(1/2, I3);
AssertWeakLocal(A, Poly, 2, "polynomial weak inverse");
if MatMulLocal(A, Poly) <> MatMulLocal(Poly, A) then Error("polynomial should commute"); fi;
if Poly = D then Error("polynomial weak inverse should differ from Drazin inverse"); fi;

Proj := [[1/2,2,3],[0,0,5],[0,0,7]];
AssertWeakLocal(A, Proj, 2, "projective-shaped weak inverse");
BA := MatMulLocal(Proj, A);
if BA <> [[1,0,2],[0,0,0],[0,0,0]] then Error("projective BA readout failed"); fi;
if MatMulLocal(BA, BA) <> BA then Error("projective BA idempotence failed"); fi;

CommWeak := [[1/2,0,0],[0,3,4],[0,0,3]];
AssertWeakLocal(A, CommWeak, 2, "commuting weak inverse");
if MatMulLocal(A, CommWeak) <> MatMulLocal(CommWeak, A) then Error("commuting packet failed"); fi;

P := [[0,0,1],[0,1,0],[1,0,0]];
AssertWeakLocal(MatMulLocal(MatMulLocal(P, A), P), MatMulLocal(MatMulLocal(P, Poly), P), 2,
  "GL_3(Q) conjugate");

Print("CAMPBELL_MEYER_WEAK_DRAZIN_GAP_CERTIFICATE_OK\n");
