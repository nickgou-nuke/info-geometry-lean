Print("=== GAP GNSD staircase / Drazin certificate ===\n");

MatMul := function(A, B)
  return A * B;
end;

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

JordanZero := function(k)
  local A, i;
  A := ZeroMatQ(k, k);
  for i in [1..k-1] do
    A[i][i+1] := 1;
  od;
  return A;
end;

BlockDiag3 := function(A, B, C)
  local zAB, zAC, zBA, zBC, zCA, zCB;
  zAB := ZeroMatQ(Length(A), Length(B));
  zAC := ZeroMatQ(Length(A), Length(C));
  zBA := ZeroMatQ(Length(B), Length(A));
  zBC := ZeroMatQ(Length(B), Length(C));
  zCA := ZeroMatQ(Length(C), Length(A));
  zCB := ZeroMatQ(Length(C), Length(B));
  return Concatenation(
    List([1..Length(A)], i -> Concatenation(A[i], zAB[i], zAC[i])),
    List([1..Length(B)], i -> Concatenation(zBA[i], B[i], zBC[i])),
    List([1..Length(C)], i -> Concatenation(zCA[i], zCB[i], C[i]))
  );
end;

Block2 := function(A, B, C, D)
  return Concatenation(
    List([1..Length(A)], i -> Concatenation(A[i], B[i])),
    List([1..Length(C)], i -> Concatenation(C[i], D[i]))
  );
end;

Nullity := function(A)
  return Length(A[1]) - RankMat(A);
end;

A := BlockDiag3(JordanZero(3), JordanZero(2), JordanZero(1));
nullities := List([0..3], j -> Nullity(MatPow(A, j)));
if nullities <> [0, 3, 5, 6] then
  Error("nullity staircase failed");
fi;
mu := [nullities[2] - nullities[1], nullities[3] - nullities[2], nullities[4] - nullities[3]];
if mu <> [3, 2, 1] then
  Error("GNSD mu increments failed");
fi;
Print("PASS: nullity increments recover GNSD block-size counts\n");

N := [[0, 1], [0, 0]];
M := [[2, 1], [0, 3]];
MI := M^-1;
K := [[1, 2], [-1, 1]];
L := K * M - N * K;
Zm := ZeroMatQ(2, 2);
I2 := IdentityMat(2);
B := Block2(N, L, Zm, M);
S := Block2(I2, K, Zm, I2);
Sinv := Block2(I2, -K, Zm, I2);
DiagNM := Block2(N, Zm, Zm, M);
if Sinv * B * S <> DiagNM then
  Error("Sylvester decoupling failed");
fi;
Print("PASS: Sylvester shear decouples the GNSD block\n");

D := Block2(Zm, K * MI, Zm, MI);
if D * B * D <> D then
  Error("D B D = D failed");
fi;
if B * D <> D * B then
  Error("B D = D B failed");
fi;
if MatPow(B, 3) * D <> MatPow(B, 2) then
  Error("B^3 D = B^2 failed");
fi;
Print("PASS: Drazin block formula satisfies index-2 laws\n");

Print("GNSD_GAP_CERTIFICATE_OK\n");
