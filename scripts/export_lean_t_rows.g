F := GF(2);;
entry := function(j, r)
  if j in r then return One(F); fi;
  return Zero(F);
end;;
M := function(rows)
  return List(rows, r -> List([1..8], j ->
    entry(j, r)));
end;;

leanGens := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];;

s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);;
cycle := M([[1],[2],[4],[5],[3],[7],[8],[6]]);;
cartan := M([[2],[1],[6],[7],[8],[3],[4],[5]]);;
c := cycle * cartan;;
# Lean automorphism multiplication is reverse matrix composition: t = s*c
t := c * s;;
for i in [1..8] do
  Print("TROW ", i, " ");
  for j in [1..8] do
    if t[i][j] <> Zero(F) then Print(j); fi;
    if j < 8 then Print(","); fi;
  od;
  Print("\n");
od;
QUIT;
