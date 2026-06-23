Print("=== GAP Campbell 1977 continuity audit ===\n");

ZeroMatQ := function(n, m)
  return List([1..n], i -> List([1..m], j -> 0));
end;

OneNorm := function(A)
  local m, n, best, j, s, i;
  m := Length(A);
  n := Length(A[1]);
  best := 0;
  for j in [1..n] do
    s := 0;
    for i in [1..m] do
      s := s + AbsInt(NumeratorRat(A[i][j])) / DenominatorRat(A[i][j]);
    od;
    if s > best then best := s; fi;
  od;
  return best;
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

A := [[1, 2, 3], [2, 4, 6]];
Ap := [[1/70, 1/35], [1/35, 2/35], [3/70, 3/35]];
F := [[1/100, 0], [-1/150, 1/90], [0, 1/120]];
Xmp := Ap + F;
Im := IdentityMat(2);
In := IdentityMat(3);
E1 := A * Xmp * A - A;
E2 := Xmp * A * Xmp - Xmp;
E3 := A * Xmp - TransposedMat(Xmp) * TransposedMat(A);
E4 := Xmp * A - TransposedMat(A) * TransposedMat(Xmp);
Rhs := Ap * E1 * Ap
  + (In - Ap * A) * E4 * Ap
  + Ap * E3 * (Im - A * Ap)
  + (In - Ap * A) * (-E2 + E4 * Ap * E3) * (Im - A * Ap);
AssertZeroMat(F - Rhs, "Moore-Penrose residual decomposition");
Bound := OneNorm(E1) * OneNorm(Ap)^2
  + OneNorm(E2) * OneNorm(Ap * A) * OneNorm(Im - A * Ap)
  + OneNorm(E4) * OneNorm(In - Ap * A) * OneNorm(Ap)
  + (OneNorm(E2) + OneNorm(E4) * OneNorm(Ap) * OneNorm(E3))
    * OneNorm(In - Ap * A) * OneNorm(Im - A * Ap);
if OneNorm(F) > Bound then Error("Moore-Penrose one-norm bound failed"); fi;
Print("PASS: Moore-Penrose residual decomposition and 1-norm bound\n");

G := [[1, 0], [0, 0]];
Gg := G;
Fg := [[1/50, 1/80], [-1/70, 1/60]];
Xg := Gg + Fg;
I2 := IdentityMat(2);
P := Gg * G;
D1 := Xg * G * Xg - Xg;
D2 := Xg * G - G * Xg;
D3 := G^2 * Xg - G;
RhsG := Gg * Gg * D3 * P
  + -Gg * D2 * (I2 - P)
  + (I2 - P) * D2 * Gg
  + (I2 - P) * (-D2 * Gg * D2 - D1) * (I2 - P);
AssertZeroMat(Fg - RhsG, "group-inverse residual decomposition");
BoundG := OneNorm(Gg)^2 * OneNorm(D3)
  + OneNorm(Gg) * OneNorm(D2) * OneNorm(I2 - P)
  + OneNorm(I2 - P) * OneNorm(D2) * OneNorm(Gg)
  + (OneNorm(D1) + OneNorm(D2)^2 * OneNorm(Gg)) * OneNorm(I2 - P)^2;
if OneNorm(Fg) > BoundG then Error("group-inverse one-norm bound failed"); fi;
Print("PASS: group-inverse residual decomposition and 1-norm bound\n");

Print("CAMPBELL1977_GAP_AUDIT_OK\n");
