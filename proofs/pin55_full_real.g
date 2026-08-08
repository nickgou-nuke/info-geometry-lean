# GAP certificate for the finite signed-monomial shadow of Pin(5,5).
# The abstract Clifford generators have the correct positive/negative squares
# and anticommutation central sign.  Their twisted vector images are the ten
# coordinate reflections in O(5,5).

F := FreeGroup("z", "g1", "g2", "g3", "g4", "g5",
               "g6", "g7", "g8", "g9", "g10");;
gensF := GeneratorsOfGroup(F);;
z := gensF[1];;
gs := gensF{[2..11]};;
rels := [z^2];;
for g in gs do Add(rels, Comm(z,g)); od;
for i in [1..5] do Add(rels, gs[i]^2); od;
for i in [6..10] do Add(rels, gs[i]^2/z); od;
for i in [1..10] do
  for j in [i+1..10] do
    Add(rels, gs[i]*gs[j]/(z*gs[j]*gs[i]));
  od;
od;
PinMon := F/rels;;

eta := DiagonalMat(Concatenation(List([1..5],i->1),List([1..5],i->-1)));;
refs := [];;
for i in [1..10] do
  r := IdentityMat(10, Rationals);
  r[i][i] := -1;
  Add(refs,r);
  if TransposedMat(r)*eta*r <> eta then Error("metric failure"); fi;
  if DeterminantMat(r) <> -1 then Error("determinant failure"); fi;
od;
H := Group(refs);;
gensPin := GeneratorsOfGroup(PinMon);;
rho := GroupHomomorphismByImages(PinMon,H,gensPin,
          Concatenation([IdentityMat(10,Rationals)],refs));;
if rho = fail then Error("homomorphism construction failure"); fi;
if not IsSurjective(rho) then Error("finite reflection image not surjective"); fi;
if Size(PinMon) <> 2048 then Error("signed Clifford monomial order"); fi;
if Size(H) <> 1024 then Error("coordinate reflection image order"); fi;
if Size(Kernel(rho)) <> 2 then Error("central sign kernel order"); fi;

Print("pin55_full_real.g: PASS\n");
Print("signed Clifford monomial group order: ",Size(PinMon),"\n");
Print("coordinate reflection image order: ",Size(H),"\n");
Print("finite shadow kernel order: ",Size(Kernel(rho)),"\n");
QUIT;
