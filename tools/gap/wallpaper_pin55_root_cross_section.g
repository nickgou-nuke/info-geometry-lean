# Exact-rational GAP certificate for the wallpaper/Pin(5,5) root cross-section.

MatKey := M -> M;;
VecNeg := v -> List(v, x -> -x);;
MatVec := function(M, v)
  return List([1..Length(M)], i -> Sum([1..Length(v)], j -> M[i][j] * v[j]));
end;;
BlockDiag := function(A, B)
  local n, m, Z, i, j;
  n := Length(A);
  m := Length(B);
  Z := NullMat(n + m, n + m, Rationals);
  for i in [1..n] do
    for j in [1..n] do
      Z[i][j] := A[i][j];
    od;
  od;
  for i in [1..m] do
    for j in [1..m] do
      Z[n+i][n+j] := B[i][j];
    od;
  od;
  return Z;
end;;

I2 := IdentityMat(2, Rationals);;
I5 := IdentityMat(5, Rationals);;
T := [[0,-1],[1,0]];;
G := [[1,0],[0,-1]];;
D4 := [I2, T, -I2, -T, G, T*G, -G, -T*G];;

signedPerm2 := [];;
for p in [[1,2],[2,1]] do
  for s1 in [1,-1] do
    for s2 in [1,-1] do
      M := NullMat(2, 2, Rationals);;
      M[p[1]][1] := s1;;
      M[p[2]][2] := s2;;
      Add(signedPerm2, M);;
    od;
  od;
od;

compatible := Filtered(signedPerm2,
  S -> TransposedMat(S) * S = I2 and (S*T = T*S or S*T = -T*S));;
if Set(compatible) <> Set(D4) then Error("compatible wallpaper D4 classification failed"); fi;
if Length(Set(D4)) <> 8 then Error("D4 cardinality failed"); fi;
for A in D4 do
  for B in D4 do
    if not ((A*B) in D4) then Error("D4 closure failed"); fi;
  od;
od;

b2Roots := [[1,0],[-1,0],[0,1],[0,-1],[1,1],[-1,-1],[1,-1],[-1,1]];;
b2Set := Set(b2Roots);;
for S in D4 do
  for r in b2Roots do
    if not (MatVec(S, r) in b2Set) then Error("D4 root action failed"); fi;
  od;
od;

d5Roots := [];;
for i in [1..5] do
  for j in [i+1..5] do
    for si in [1,-1] do
      for sj in [1,-1] do
        r := [0,0,0,0,0];;
        r[i] := si;;
        r[j] := sj;;
        Add(d5Roots, r);;
        Add(d5Roots, VecNeg(r));;
      od;
    od;
  od;
od;
d5Set := Set(d5Roots);;
if Length(d5Set) <> 40 then Error("D5 root count failed"); fi;
projected := Set(List(d5Roots, r -> [r[1], r[2]]));;
if Difference(projected, [[0,0]]) <> b2Set then Error("D5 to B2 projection failed"); fi;

lifts := [[1,0,1,0,0],[-1,0,1,0,0],[0,1,1,0,0],[0,-1,1,0,0],
          [1,1,0,0,0],[-1,-1,0,0,0],[1,-1,0,0,0],[-1,1,0,0,0]];;
for k in [1..8] do
  if not (lifts[k] in d5Set) then Error("B2 lift not a D5 root"); fi;
  if [lifts[k][1], lifts[k][2]] <> b2Roots[k] then Error("B2 lift projection failed"); fi;
od;

cross := [
  I5,
  [[0,-1,0,0,0],[1,0,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
  DiagonalMat([-1,-1,1,1,1]),
  [[0,1,0,0,0],[-1,0,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
  DiagonalMat([1,-1,-1,1,1]),
  [[0,1,0,0,0],[1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
  DiagonalMat([-1,1,-1,1,1]),
  [[0,-1,0,0,0],[-1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]
];;
eta55 := DiagonalMat([1,1,1,1,1,-1,-1,-1,-1,-1]);;
for k in [1..8] do
  P := cross[k];;
  if TransposedMat(P) * P <> I5 then Error("D5 lift orthogonality failed"); fi;
  if [[P[1][1], P[1][2]], [P[2][1], P[2][2]]] <> D4[k] then
    Error("D5 lift projection failed");
  fi;
  for r in d5Roots do
    if not (MatVec(P, r) in d5Set) then Error("D5 root preservation failed"); fi;
  od;
  L := BlockDiag(P, P);;
  if TransposedMat(L) * eta55 * L <> eta55 then Error("O55 metric preservation failed"); fi;
od;

Print("WALLPAPER_PIN55_ROOT_CROSS_SECTION_GAP_CERTIFICATE_OK\n");
