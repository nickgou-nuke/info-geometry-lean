Print("=== GAP Hartwig 1976 Souriau--Frame / Drazin certificate ===\n");

MatPow := function(A, n)
  local r, i;
  r := IdentityMat(Length(A));
  for i in [1..n] do
    r := r * A;
  od;
  return r;
end;

ZeroMatQ := function(n, m)
  return List([1..n], i -> List([1..m], j -> 0));
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

A := [[0, 0, 0], [0, 2, 0], [0, 0, 3]];
I3 := IdentityMat(3);
A0 := [[6, 0, 0], [0, 0, 0], [0, 0, 0]];
A1 := [[-5, 0, 0], [0, -3, 0], [0, 0, -2]];

Xg := (I3 - (1/6) * A0) * ((-1/6) * A1);
Expected := [[0, 0, 0], [0, 1/2, 0], [0, 0, 1/3]];
if Xg <> Expected then
  Error("Hartwig formula did not produce the expected group inverse");
fi;
Print("PASS: Hartwig coefficient formula gives A#\n");

AssertZeroMat(A * Xg * A - A, "A X A = A");
AssertZeroMat(Xg * A * Xg - Xg, "X A X = X");
AssertZeroMat(A * Xg - Xg * A, "A X = X A");
AssertZeroMat(MatPow(A, 2) * Xg - A, "A^2 X = A");
Print("PASS: group inverse and Drazin index-one laws\n");

Zg := I3 - A * Xg;
if Zg <> [[1, 0, 0], [0, 0, 0], [0, 0, 0]] then
  Error("principal idempotent readout failed");
fi;
AssertZeroMat(Zg * Zg - Zg, "Z^2 = Z");
AssertZeroMat(A * Zg, "A Z = 0");
AssertZeroMat(Zg * A, "Z A = 0");
Print("PASS: principal idempotent selects the zero-root lane\n");

P := [[0, 1, 0], [1, 0, 0], [0, 0, 1]];
Pinv := P^-1;
Ac := P * A * Pinv;
Xc := P * Xg * Pinv;
AssertZeroMat(Ac * Xc * Ac - Ac, "conjugated A X A = A");
AssertZeroMat(Xc * Ac * Xc - Xc, "conjugated X A X = X");
AssertZeroMat(Ac * Xc - Xc * Ac, "conjugated commutation");
Print("PASS: GL_3 conjugation preserves the group-inverse representation\n");

Print("HARTWIG1976_GAP_CERTIFICATE_OK\n");
