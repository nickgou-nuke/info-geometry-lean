Print("=== GAP Greville 1973 Souriau--Frame / Drazin certificate ===\n");

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

TraceMat3Local := function(A)
  local s, i;
  s := 0;
  for i in [1..Length(A)] do
    s := s + A[i][i];
  od;
  return s;
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

A := [[0, 1, 0], [0, 0, 0], [0, 0, 2]];
I3 := IdentityMat(3);
B0 := I3;
p1 := TraceMat3Local(A * B0);
B1 := A * B0 - p1 * I3;
p2 := (1/2) * TraceMat3Local(A * B1);
B2 := A * B1 - p2 * I3;
p3 := (1/3) * TraceMat3Local(A * B2);
B3 := A * B2 - p3 * I3;

if p1 <> 2 or p2 <> 0 or p3 <> 0 then
  Error("Souriau--Frame scalar recurrence failed");
fi;
if B2 = ZeroMatQ(3, 3) then
  Error("B2 should be nonzero");
fi;
if B3 <> ZeroMatQ(3, 3) then
  Error("B3 should be zero");
fi;
Print("PASS: Souriau--Frame recurrence has r=3, s=1, k=2\n");

k := 2;
Xg := (p1 ^ (-(k + 1))) * MatPow(A, k) * MatPow(B0, k + 1);
Expected := [[0, 0, 0], [0, 0, 0], [0, 0, 1/2]];
if Xg <> Expected then
  Error("Greville formula did not produce the expected Drazin inverse");
fi;
Print("PASS: Greville formula gives A^D\n");

AssertZeroMat(A * Xg - Xg * A, "A X = X A");
AssertZeroMat(Xg * A * Xg - Xg, "X A X = X");
AssertZeroMat(MatPow(A, k + 1) * Xg - MatPow(A, k), "A^(k+1) X = A^k");
AssertZeroMat(A * Xg * Xg - Xg, "A X^2 = X");
Print("PASS: Drazin index-2 laws\n");

Regular := A * Xg;
Nilpotent := I3 - Regular;
if Regular <> [[0, 0, 0], [0, 0, 0], [0, 0, 1]] then
  Error("regular projector readout failed");
fi;
if Nilpotent <> [[1, 0, 0], [0, 1, 0], [0, 0, 0]] then
  Error("nilpotent projector readout failed");
fi;
AssertZeroMat(Regular * Regular - Regular, "regular projector");
AssertZeroMat(Nilpotent * Nilpotent - Nilpotent, "nilpotent projector");
AssertZeroMat(MatPow(A * Nilpotent, 2), "nilpotent lane square-zero");
Print("PASS: Drazin projectors split the two lanes\n");

P := [[0, 0, 1], [0, 1, 0], [1, 0, 0]];
Pinv := P^-1;
Ac := P * A * Pinv;
Xc := P * Xg * Pinv;
AssertZeroMat(Ac * Xc - Xc * Ac, "conjugated commutation");
AssertZeroMat(Xc * Ac * Xc - Xc, "conjugated X A X = X");
AssertZeroMat(MatPow(Ac, k + 1) * Xc - MatPow(Ac, k), "conjugated power law");
Print("PASS: GL_3(Q) conjugation preserves the packet\n");

Print("GREVILLE1973_GAP_CERTIFICATE_OK\n");
