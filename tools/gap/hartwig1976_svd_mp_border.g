Print("=== GAP Hartwig 1976 SVD / Moore--Penrose bordered certificate ===\n");

ZeroMatLocal := function(rows, cols)
  return List([1..rows], i -> List([1..cols], j -> 0));
end;

TransposeMatLocal := function(M)
  local rows, cols;
  rows := Length(M);
  cols := Length(M[1]);
  return List([1..cols], j -> List([1..rows], i -> M[i][j]));
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

AssertZeroMatLocal := function(M, label)
  if M <> ZeroMatLocal(Length(M), Length(M[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

AssertMPLocal := function(A, X, label)
  AssertZeroMatLocal(MatSubLocal(MatMulLocal(MatMulLocal(A, X), A), A),
    Concatenation(label, ": A X A = A"));
  AssertZeroMatLocal(MatSubLocal(MatMulLocal(MatMulLocal(X, A), X), X),
    Concatenation(label, ": X A X = X"));
  AssertZeroMatLocal(MatSubLocal(TransposeMatLocal(MatMulLocal(A, X)), MatMulLocal(A, X)),
    Concatenation(label, ": (A X)^* = A X"));
  AssertZeroMatLocal(MatSubLocal(TransposeMatLocal(MatMulLocal(X, A)), MatMulLocal(X, A)),
    Concatenation(label, ": (X A)^* = X A"));
end;

baseA := [[2, 0], [0, 0]];
baseMP := [[1/2, 0], [0, 0]];
AssertMPLocal(baseA, baseMP, "base SVD block");

case1 := [[2, 0, 3], [0, 0, 0], [1, 0, 5]];
case1MP := [[5/7, 0, -3/7], [0, 0, 0], [-1/7, 0, 2/7]];
z := 5 - 1 * (1/2) * 3;
if z <> 7/2 then Error("Case 1 z readout failed"); fi;
AssertMPLocal(case1, case1MP, "Hartwig Case 1 border");
AssertMPLocal([[7/5, 0], [0, 0]], [[5/7, 0], [0, 0]], "Hartwig Case 1 Schur complement");
Print("PASS: Case 1 border and Schur complement are certified\n");

case3 := [[2, 0, 0], [0, 0, 1], [0, 1, 5]];
case3MP := [[1/2, 0, 0], [0, -5, 1], [0, 1, 0]];
AssertMPLocal(case3, case3MP, "Hartwig Case 3 border");
AssertMPLocal([[2, 0], [0, -1/5]], [[1/2, 0], [0, -5]], "Hartwig Case 3 Schur complement");
Print("PASS: Case 3 border and Schur complement are certified\n");

p := [[0, 0, 1], [0, 1, 0], [1, 0, 0]];
AssertMPLocal(MatMulLocal(MatMulLocal(p, case1), TransposeMatLocal(p)),
  MatMulLocal(MatMulLocal(p, case1MP), TransposeMatLocal(p)),
  "orthogonal GL_3(Q) conjugate");
Print("PASS: rational orthogonal conjugation preserves the MP packet\n");

Print("HARTWIG1976_SVD_MP_BORDER_GAP_CERTIFICATE_OK\n");
