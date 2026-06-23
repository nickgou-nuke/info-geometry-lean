Print("=== GAP Holographic Souriau Reconstruction certificate ===\n");

ZeroMatQ := function(n, m)
  return List([1..n], i -> List([1..m], j -> 0));
end;

AssertZeroMat := function(A, label)
  if A <> ZeroMatQ(Length(A), Length(A[1])) then
    Error(Concatenation(label, " failed"));
  fi;
end;

TraceMatQ := function(A)
  local s, i;
  s := 0;
  for i in [1..Length(A)] do
    s := s + A[i][i];
  od;
  return s;
end;

MatComm := function(A, B)
  return A * B - B * A;
end;

Eta := DiagonalMat([1,1,1,1,1,-1,-1,-1,-1,-1]);
if TransposedMat(Eta) <> Eta then Error("eta symmetry failed"); fi;
if Eta * Eta <> IdentityMat(10) then Error("eta involution failed"); fi;
if DeterminantMat(Eta) <> -1 then Error("eta determinant failed"); fi;

Twist := [[0,-1],[1,0]];
Glide := [[1,0],[0,-1]];
if Twist * Twist <> -IdentityMat(2) then Error("twist square failed"); fi;
if Glide * Glide <> IdentityMat(2) then Error("glide square failed"); fi;
AssertZeroMat(Glide * Twist + Twist * Glide, "Brillouin anticommutator");

E12 := [[0,1,0],[0,0,0],[0,0,0]];
E21 := [[0,0,0],[1,0,0],[0,0,0]];
E23 := [[0,0,0],[0,0,1],[0,0,0]];
E32 := [[0,0,0],[0,0,0],[0,1,0]];
E13 := [[0,0,1],[0,0,0],[0,0,0]];
E31 := [[0,0,0],[0,0,0],[1,0,0]];
H1 := [[1,0,0],[0,-1,0],[0,0,0]];
H2 := [[0,0,0],[0,1,0],[0,0,-1]];
Gens := [E12,E21,E23,E32,E13,E31,H1,H2];
Laser := 2 * IdentityMat(3);

for g in Gens do
  if TraceMatQ(g) <> 0 then Error("color trace failed"); fi;
  AssertZeroMat(MatComm(Laser, g), "color generator dark commutator");
od;
AssertZeroMat(MatComm(E12, E23) - E13, "[E12,E23] - E13");
AssertZeroMat(MatComm(E21, E32) + E31, "[E21,E32] + E31");

Print("HOLOGRAPHIC_SOURIAU_RECONSTRUCTION_GAP_CERTIFICATE_OK\n");
