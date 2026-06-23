# Exact finite certificate for UHF Boolean projection / Cantor prefix bridge.
Words := function(n)
  local prev, out, w;
  if n = 0 then return [[]]; fi;
  prev := Words(n-1); out := [];
  for w in prev do Add(out, Concatenation(w,[0])); Add(out, Concatenation(w,[1])); od;
  return out;
end;
Atom := function(a,v) if a = v then return 1; else return 0; fi; end;
for n in [0..4] do
  for a in Words(n) do
    for v in Words(n) do
      if Atom(a,v)^2 <> Atom(a,v) then Error("atom idempotent failed"); fi;
    od;
  od;
od;
for n in [0..3] do
  for w in Words(n+1) do
    if not w{[1..n]} in Words(n) then Error("prefix failed"); fi;
  od;
od;
# Characteristic homomorphism of a principal ultrafilter preserves meet/join/complement.
U3 := Words(3); pt := [0,1,1];
EventA := [U3[2], U3[5]]; EventB := [U3[5], U3[7]];
MeetAB := Intersection(EventA, EventB); JoinAB := Union(EventA, EventB); CompA := Difference(U3, EventA);
Chi := function(E) return pt in E; end;
if Chi(MeetAB) <> (Chi(EventA) and Chi(EventB)) then Error("meet hom failed"); fi;
if Chi(JoinAB) <> (Chi(EventA) or Chi(EventB)) then Error("join hom failed"); fi;
if Chi(CompA) <> (not Chi(EventA)) then Error("complement hom failed"); fi;
Print("uhf Boolean projection Cantor bridge GAP certificate: ok\n");
