Print("=== GAP Decell Cayley-Hamilton generalized inverse certificate ===\n");

ZeroMatQ := function(n, m)
  return List([1..n], i -> List([1..m], j -> 0));
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

CheckPenrose := function(A, Ap, label)
  AssertZeroMat(A * Ap * A - A, Concatenation(label, ": A A+ A = A"));
  AssertZeroMat(Ap * A * Ap - Ap, Concatenation(label, ": A+ A A+ = A+"));
  AssertZeroMat(TransposedMat(A * Ap) - A * Ap, Concatenation(label, ": A A+ symmetric"));
  AssertZeroMat(TransposedMat(Ap * A) - Ap * A, Concatenation(label, ": A+ A symmetric"));
  Print("PASS: ", label, "\n");
end;

A1 := [[1, 2, 3], [2, 4, 6]];
Ap1 := [[1/70, 1/35], [1/35, 2/35], [3/70, 3/35]];
CheckPenrose(A1, Ap1, "rank-one rectangular 2x3");

A2 := [[1, 2], [3, 5]];
Ap2 := [[-5, 2], [3, -1]];
CheckPenrose(A2, Ap2, "invertible square 2x2");

A3 := [[1, 0, 1], [0, 1, 1], [1, 1, 2]];
Ap3 := [[5/9, -4/9, 1/9], [-4/9, 5/9, 1/9], [1/9, 1/9, 2/9]];
CheckPenrose(A3, Ap3, "rank-two symmetric 3x3");

A0 := [[0, 0, 0], [0, 0, 0]];
Ap0 := [[0, 0], [0, 0], [0, 0]];
CheckPenrose(A0, Ap0, "zero rectangular 2x3");

Print("DECELL_CAYLEY_HAMILTON_GAP_CERTIFICATE_OK\n");
