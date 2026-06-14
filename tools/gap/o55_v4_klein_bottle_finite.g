# GAP exact finite matrix witnesses for O(5,5)/V4/Klein-bottle shadows.

RequireTrue := function(label, cond)
  if not cond then
    Error(Concatenation(label, " failed"));
  fi;
  Print(label, " OK\n");
end;

DiagWithFlips := function(indices)
  local m, i;
  m := IdentityMat(10, Rationals);
  for i in indices do
    m[i][i] := -1;
  od;
  return m;
end;

# Hyperbolic form matrix J with blocks [[0,I],[I,0]].
J := NullMat(10, 10, Rationals);
for i in [1..5] do
  J[i][i+5] := 1;
  J[i+5][i] := 1;
od;

I := IdentityMat(10, Rationals);
neg := -I;
r0 := DiagWithFlips([1,6]);
r1 := DiagWithFlips([2,7]);

for pair in [["neg", neg], ["r0", r0], ["r1", r1], ["r0r1", r0 * r1]] do
  RequireTrue(Concatenation("GAP_O55_", pair[1], "_PAIRING"), pair[2] * J * TransposedMat(pair[2]) = J);
  RequireTrue(Concatenation("GAP_O55_", pair[1], "_INVOLUTIVE"), pair[2] * pair[2] = I);
od;

RequireTrue("GAP_O55_V4_COMMUTING_INVOLUTIONS", r0 * r1 = r1 * r0);

# Affine Klein bottle relation on coordinate 1:
# r(t_a(r(x))) = t_{-a}(x).  Linear part is identity; offset is -a e1.
rAff := DiagWithFlips([1]);
e1 := List([1..10], i -> 0);;
e1[1] := 1;;
# homogeneous affine matrices [A b; 0 1]
Affine := function(A, b)
  local M, i, j;
  M := NullMat(11, 11, Rationals);
  for i in [1..10] do
    for j in [1..10] do
      M[i][j] := A[i][j];
    od;
    M[i][11] := b[i];
  od;
  M[11][11] := 1;
  return M;
end;

T1 := Affine(I, e1);
Tm1 := Affine(I, -e1);
Raff := Affine(rAff, List([1..10], i -> 0));
RequireTrue("GAP_O55_KLEIN_BOTTLE_AFFINE_RELATION", Raff * T1 * Raff = Tm1);

Print("GAP_O55_V4_KLEIN_PACKET_OK\n");
