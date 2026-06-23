Print("=== GAP Rose 1976 Drazin polynomial audit ===\n");

ZeroMatQ := function(n, m)
  return List([1..n], i -> List([1..m], j -> 0));
end;

BlockDiag2 := function(A, B)
  local Z12, Z21, top, bot;
  Z12 := ZeroMatQ(Length(A), Length(B[1]));
  Z21 := ZeroMatQ(Length(B), Length(A[1]));
  top := List([1..Length(A)], i -> Concatenation(A[i], Z12[i]));
  bot := List([1..Length(B)], i -> Concatenation(Z21[i], B[i]));
  return Concatenation(top, bot);
end;

MatPow := function(A, n)
  local r, i;
  r := IdentityMat(Length(A));
  for i in [1..n] do r := r * A; od;
  return r;
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

N := [[0, 1], [0, 0]];
C := [[0, -1], [1, -5]];
A := BlockDiag2(N, C);
I2 := IdentityMat(2);
I4 := IdentityMat(4);

AssertZeroMat(N^2, "N^2 = 0");
AssertZeroMat(C^2 + 5*C + I2, "C^2+5C+I=0");

Xd := A^2 * (-24*A - 115*I4);
Expected := BlockDiag2(ZeroMatQ(2, 2), -C - 5*I2);
AssertZeroMat(Xd - Expected, "Rose polynomial equals block Drazin candidate");

AssertZeroMat(A*Xd - Xd*A, "A X = X A");
AssertZeroMat(Xd*A*Xd - Xd, "X A X = X");
AssertZeroMat(MatPow(A, 3)*Xd - A^2, "A^(k+1) X = A^k");
Print("ROSE1976_GAP_AUDIT_OK\n");
