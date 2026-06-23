# Exact-rational GAP certificate for Klein-compatible wallpaper symmetries.

T := [[0,-1],[1,0]];;
G := [[1,0],[0,-1]];;
I := IdentityMat(2, Rationals);;
D4 := [I, T, -I, -T, G, T*G, -G, -T*G];;
if T*T <> -I then Error("twist square failed"); fi;
if G*G <> I then Error("glide square failed"); fi;
if G*T <> -T*G then Error("anticommutation failed"); fi;
for S in D4 do
  if TransposedMat(S) * S <> I then Error("orthogonality failed"); fi;
  if not (S*T = T*S or S*T = -T*S) then Error("Klein compatibility failed"); fi;
  if S*(T*T) <> -S then Error("twist-square preservation failed"); fi;
od;
if Length(Set(D4)) <> 8 then Error("D4 cardinality failed"); fi;
for A in D4 do
  for B in D4 do
    if not ((A*B) in D4) then Error("D4 closure failed"); fi;
  od;
od;
Print("wallpaper Klein-bottle Cartan GAP certificate: ok\n");
