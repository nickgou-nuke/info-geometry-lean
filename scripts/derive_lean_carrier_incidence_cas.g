# Exact incidence certificate for the Lean-aligned 8x8 carrier.
# The matrices below are the carrier used by the Lean PC/CAS alignment owners.
# This script is the CAS source for a future Lean incidence transport; it does
# not assert a theorem in Lean.

F := GF(2);
entry := function(j, support)
  if j in support then return One(F); else return Zero(F); fi;
end;
M := function(rows)
  return List(rows, r -> List([1..8], j -> entry(j, r)));
end;

pcgens := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);
cycle := M([[1],[2],[4],[5],[3],[7],[8],[6]]);
cartan := M([[2],[1],[6],[7],[8],[3],[4],[5]]);
correctedT := cycle^2 * s * cartan;

B := Group(pcgens);
G := Group(Concatenation(pcgens, [s, correctedT]));
Pshort := Group(Concatenation(pcgens, [s]));
Plong := Group(Concatenation(pcgens, [correctedT]));

if Size(B) <> 64 then Error("LEAN_B_SIZE failed"); fi;
if Size(G) <> 12096 then Error("LEAN_G_SIZE failed"); fi;
if Size(Pshort) <> 192 or Size(Plong) <> 192 then
  Error("LEAN_PARABOLIC_SIZE failed");
fi;

points := RightCosets(G, Pshort);
lines := RightCosets(G, Plong);
if Length(points) <> 63 or Length(lines) <> 63 then
  Error("LEAN_PARABOLIC_INDEX failed");
fi;

incidence := [];
for i in [1..Length(points)] do
  row := [];
  for j in [1..Length(lines)] do
    if Intersection(points[i], lines[j]) <> [] then Add(row, j-1); fi;
  od;
  Add(incidence, row);
od;

pointDegrees := List(incidence, Length);
lineDegrees := List([0..62], j -> Number(incidence, row -> j in row));
flagCount := Sum(pointDegrees);

if not ForAll(pointDegrees, d -> d = 3) then
  Error("LEAN_INCIDENT_POINT_DEGREE failed");
fi;
if not ForAll(lineDegrees, d -> d = 3) then
  Error("LEAN_INCIDENT_LINE_DEGREE failed");
fi;
if flagCount <> 189 then Error("LEAN_INCIDENT_FLAG_CARD failed"); fi;

# Export the carrier action on the exact right-coset point enumeration.
# The order is intentionally kept separate from Lean's `casPointEnum`; a
# later alignment step must prove the conjugating index permutation.
pointAct := ActionHomomorphism(G, points, OnRight);
Print("LEAN_CARRIER_POINT_ACTION_BEGIN\n");
for i in [1..Length(pcgens)] do
  Print("LEAN_CARRIER_POINT_ACTION_PC_", i-1, "=");
  Print(List([1..Length(points)], j -> (j^Image(pointAct, pcgens[i])) - 1), "\n");
od;
Print("LEAN_CARRIER_POINT_ACTION_SWAP=");
Print(List([1..Length(points)], j -> (j^Image(pointAct, s)) - 1), "\n");
Print("LEAN_CARRIER_POINT_ACTION_T=");
Print(List([1..Length(points)], j -> (j^Image(pointAct, correctedT)) - 1), "\n");

Print("LEAN_CARRIER_B_SIZE=", Size(B), "\n");
Print("LEAN_CARRIER_G_SIZE=", Size(G), "\n");
Print("LEAN_CARRIER_PSHORT_SIZE=", Size(Pshort), "\n");
Print("LEAN_CARRIER_PLONG_SIZE=", Size(Plong), "\n");
Print("LEAN_CARRIER_POINT_CARD=", Length(points), "\n");
Print("LEAN_CARRIER_LINE_CARD=", Length(lines), "\n");
Print("LEAN_CARRIER_FLAG_CARD=", flagCount, "\n");
for i in [1..Length(incidence)] do
  Print("LEAN_CARRIER_INCIDENCE_", i-1, "=", incidence[i], "\n");
od;
Print("LEAN_CARRIER_INCIDENCE=PASS\n");
QUIT;
