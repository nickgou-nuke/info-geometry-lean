# Exact-rational GAP certificate for the wallpaper/Pin(5,5) root cross-section.

T := [[0,-1],[1,0]];; G := [[1,0],[0,-1]];; I2 := IdentityMat(2, Rationals);;
D4 := [I2, T, -I2, -T, G, T*G, -G, -T*G];;
B2 := [[1,0],[-1,0],[0,1],[0,-1],[1,1],[-1,-1],[1,-1],[-1,1]];;
D5 := [];;
for i in [1..5] do for j in [1..5] do if i <> j then
  for si in [1,-1] do for sj in [1,-1] do
    v := [0,0,0,0,0];; v[i] := si;; v[j] := sj;; AddSet(D5, v);
  od; od;
fi; od; od;
LIFTS := [[1,0,1,0,0],[-1,0,1,0,0],[0,1,1,0,0],[0,-1,1,0,0],
          [1,1,0,0,0],[-1,-1,0,0,0],[1,-1,0,0,0],[-1,1,0,0,0]];;
WEYL := [
IdentityMat(5,Rationals),
[[0,-1,0,0,0],[1,0,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
[[-1,0,0,0,0],[0,-1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
[[0,1,0,0,0],[-1,0,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
[[1,0,0,0,0],[0,-1,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
[[0,1,0,0,0],[1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
[[-1,0,0,0,0],[0,1,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
[[0,-1,0,0,0],[-1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]];;
if ForAny(LIFTS, l -> not l in D5) then Error("lift not D5 root"); fi;
for k in [1..8] do
  W := WEYL[k];; M := D4[k];;
  if TransposedMat(W)*W <> IdentityMat(5,Rationals) then Error("orthogonal lift failed"); fi;
  for rix in [1..8] do
    r := B2[rix];; l := LIFTS[rix];;
    image2 := M*r;; image5 := W*l;;
    if not image2 in B2 then Error("B2 preservation failed"); fi;
    if not image5 in D5 then Error("D5 preservation failed"); fi;
    if [image5[1], image5[2]] <> image2 then Error("projection mismatch"); fi;
  od;
od;
Print("wallpaper Pin55 root cross-section GAP certificate: ok\n");
