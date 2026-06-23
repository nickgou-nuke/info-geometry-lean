Print("=== GAP Smith 1977 block-circulant Moore-Penrose certificate ===\n");

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

Q := [
  [0, 0, 1, 0, 0, 0],
  [0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 1],
  [1, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0]
];

A := [
  [1, 0, 1, 0, 0, 0],
  [0, 2, 0, 0, 0, 1],
  [0, 0, 1, 0, 1, 0],
  [0, 1, 0, 2, 0, 0],
  [1, 0, 0, 0, 1, 0],
  [0, 0, 0, 1, 0, 2]
];

Ap := [
  [1/2, 0, -1/2, 0, 1/2, 0],
  [0, 4/9, 0, 1/9, 0, -2/9],
  [1/2, 0, 1/2, 0, -1/2, 0],
  [0, -2/9, 0, 4/9, 0, 1/9],
  [-1/2, 0, 1/2, 0, 1/2, 0],
  [0, 1/9, 0, -2/9, 0, 4/9]
];

I6 := IdentityMat(6);

AssertZeroMat(A * Q - Q * A, "A block-circulant shift commutator");
AssertZeroMat(Ap * Q - Q * Ap, "A+ block-circulant shift commutator");
if A * Ap <> I6 then Error("A * A+ inverse check failed"); fi;
if Ap * A <> I6 then Error("A+ * A inverse check failed"); fi;
CheckPenrose(A, Ap, "Smith 1977 rational block-circulant witness");

Print("SMITH1977_BLOCK_CIRCULANT_GAP_CERTIFICATE_OK\n");
