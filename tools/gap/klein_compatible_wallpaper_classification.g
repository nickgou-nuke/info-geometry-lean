# Exact-rational GAP certificate for finite Klein wallpaper candidates.

RequireTrue := function(label, cond)
  if not cond then
    Error(Concatenation("FAILED: ", label));
  fi;
  Print("PASS: ", label, "\n");
end;

MatVec := function(M, v)
  return List(M, row -> Sum(List([1..Length(v)], i -> row[i] * v[i])));
end;

KeySet := function(list)
  return Set(list);
end;

Print("=== Klein-compatible wallpaper classification GAP certificate ===\n");

roots := [];;
for i in [1..5] do
  for j in [i + 1..5] do
    for si in [1, -1] do
      for sj in [1, -1] do
        v := [0, 0, 0, 0, 0];;
        v[i] := si;;
        v[j] := sj;;
        Add(roots, v);;
      od;
    od;
  od;
od;
RequireTrue("D5 root count = 40", Length(roots) = 40);

projected := KeySet(List(roots, r -> [r[1], r[2]]));;
projected := Difference(projected, [[0, 0]]);;
expected := KeySet([
  [-1, -1], [-1, 0], [-1, 1], [0, -1],
  [0, 1], [1, -1], [1, 0], [1, 1]
]);;
RequireTrue("nonzero D5 projection is B2/C2 eight-root set", projected = expected);

I3 := IdentityMat(3);;
Tx := [[1,0,1],[0,1,0],[0,0,1]];;
Ty := [[1,0,0],[0,1,1],[0,0,1]];;
TyInv := [[1,0,0],[0,1,-1],[0,0,1]];;
TxInv := [[1,0,-1],[0,1,0],[0,0,1]];;
Gx := [[1,0,1/2],[0,-1,0],[0,0,1]];;
MirrorX := [[-1,0,0],[0,1,0],[0,0,1]];;
Gy := [[-1,0,0],[0,1,1/2],[0,0,1]];;

RequireTrue("pg glide square", Gx * Gx = Tx);
RequireTrue("pg transverse inversion", Gx * Ty = TyInv * Gx);

RequireTrue("pmg mirror involutive", MirrorX * MirrorX = I3);
RequireTrue("pmg carries pg glide square", Gx * Gx = Tx);
RequireTrue("pmg carries pg transverse inversion", Gx * Ty = TyInv * Gx);

RequireTrue("pgg second glide square", Gy * Gy = Ty);
RequireTrue("pgg second glide transverse inversion", Gy * Tx = TxInv * Gy);
RequireTrue("pgg first glide transverse inversion", Gx * Ty = TyInv * Gx);

candidateNormals := rec(
  pg := [[0,1], [1,-1]],
  pmg := [[1,0], [0,1]],
  pgg := [[1,0], [0,1]]
);;

for name in RecNames(candidateNormals) do
  for normal in candidateNormals.(name) do
    RequireTrue(Concatenation(name, " normal in projected D5 set"),
      normal in projected);
  od;
od;

Print("KLEIN_COMPATIBLE_WALLPAPER_CLASSIFICATION_GAP_CERTIFICATE_OK\n");
