Print("=== GAP Holographic tensor-factor separation certificate ===\n");

ZeroMatQ := function(n, m)
  return List([1..n], i -> List([1..m], j -> 0));
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

MatComm := function(A, B)
  return A * B - B * A;
end;

Eta := DiagonalMat([1,1,1,1,1,-1,-1,-1,-1,-1]);
Parity := -IdentityMat(10);
B := NullMat(10, 10);
B{[1..10]}{[1..10]} := IdentityMat(10);
B[1][7] := 2/3;
B[2][6] := -2/3;
Geoms := [Eta, Parity, B];

E12 := [[0,1,0],[0,0,0],[0,0,0]];
E21 := [[0,0,0],[1,0,0],[0,0,0]];
E23 := [[0,0,0],[0,0,1],[0,0,0]];
E32 := [[0,0,0],[0,0,0],[0,1,0]];
E13 := [[0,0,1],[0,0,0],[0,0,0]];
E31 := [[0,0,0],[0,0,0],[1,0,0]];
H1 := [[1,0,0],[0,-1,0],[0,0,0]];
H2 := [[0,0,0],[0,1,0],[0,0,-1]];
Colors := [E12,E21,E23,E32,E13,E31,H1,H2];

for G in Geoms do
  for C in Colors do
    AssertZeroMat(MatComm(KroneckerProduct(G, IdentityMat(3)), KroneckerProduct(IdentityMat(10), C)),
      "G tensor C commutator");
  od;
od;

Twist := [[0,-1],[1,0]];
Glide := [[1,0],[0,-1]];
TwistLift := KroneckerProduct(Twist, IdentityMat(3));
GlideLift := KroneckerProduct(Glide, IdentityMat(3));
if TwistLift * TwistLift <> -IdentityMat(6) then Error("twist lift square failed"); fi;
if GlideLift * GlideLift <> IdentityMat(6) then Error("glide lift square failed"); fi;
AssertZeroMat(GlideLift * TwistLift + TwistLift * GlideLift, "lifted Brillouin anticommutator");

for C in Colors do
  AssertZeroMat(MatComm(TwistLift, KroneckerProduct(IdentityMat(2), C)), "twist tensor C commutator");
  AssertZeroMat(MatComm(GlideLift, KroneckerProduct(IdentityMat(2), C)), "glide tensor C commutator");
od;

Print("HOLOGRAPHIC_TENSOR_FACTOR_SEPARATION_GAP_CERTIFICATE_OK\n");
