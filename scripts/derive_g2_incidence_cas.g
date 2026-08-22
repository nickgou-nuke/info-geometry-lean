# CAS certificate for the two 63-point/line parabolic geometries of G2(2).
# Incidence is nonempty intersection of a right Pshort-coset and a right
# Plong-coset.  This is the concrete building incidence, not all singular
# pairs of the ambient quadratic space.

F := GF(2);
entry := function(j, support)
  if j in support then return One(F); else return Zero(F); fi;
end;

rows := [
  [[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]],
  [[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]],
  [[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]],
  [[1],[2],[3],[4],[4,5],[6],[7,8],[8]],
  [[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]],
  [[1],[2],[3],[4],[3,5],[6,8],[7],[8]]
];
pcgens := List(rows, rs -> List([1..8], i -> List([1..8], j ->
  entry(j, rs[i]))));
s := PermutationMat((3,4)(6,7), 8, F);
r := PermutationMat((3,4,5)(6,7,8), 8, F);
h := PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F);
c := h * r;
t := s * c;
G := Group(Concatenation(pcgens, [s, r, h]));
U := Group(pcgens);

if Size(G) <> 12096 then Error("G_SIZE failed"); fi;
if Size(U) <> 64 then Error("U_SIZE failed"); fi;

Pshort := Group(Concatenation(pcgens, [s]));
Plong := Group(Concatenation(pcgens, [t]));
if Size(Pshort) <> 192 or Size(Plong) <> 192 then
  Error("PARABOLIC_SIZE failed");
fi;

points := RightCosets(G, Pshort);
lines := RightCosets(G, Plong);
if Length(points) <> 63 or Length(lines) <> 63 then
  Error("PARABOLIC_DEGREE failed");
fi;

incidence := [];
for i in [1..Length(points)] do
  row := [];
  for j in [1..Length(lines)] do
    if Intersection(points[i], lines[j]) <> [] then Add(row, j); fi;
  od;
  Add(incidence, row);
od;

pointDegrees := SortedList(List(incidence, Length));
lineDegrees := SortedList(List([1..Length(lines)], j ->
  Number(incidence, row -> j in row)));
flagCount := Sum(List(incidence, Length));


Print("DEBUG_POINT_DEGREES=", pointDegrees, "\n");
Print("DEBUG_LINE_DEGREES=", lineDegrees, "\n");
Print("DEBUG_FLAG_CARD=", flagCount, "\n");

if not ForAll(pointDegrees, d -> d = 3) or
   not ForAll(lineDegrees, d -> d = 3) then
  Error("INCIDENCE_DEGREE failed");
fi;
if flagCount <> 189 then Error("INCIDENCE_FLAG_CARD failed"); fi;

Print("G_SIZE=", Size(G), "\n");
Print("POINT_CARD=", Length(points), "\n");
Print("LINE_CARD=", Length(lines), "\n");
Print("POINT_DEGREES=", pointDegrees, "\n");
Print("LINE_DEGREES=", lineDegrees, "\n");
Print("FLAG_CARD=", flagCount, "\n");
for i in [1..Length(incidence)] do
  Print("INCIDENCE_", i-1, "=");
  Print(List(incidence[i], j -> j-1));
  Print("\n");
od;
Print("G2_INCIDENT_GEOMETRY_CAS=PASS\n");
QUIT;
