F := GF(2);
entry := function(j, support)
  if j in support then return One(F); else return Zero(F); fi;
end;
M := function(rows)
  return List(rows, r -> List([1..8], j -> entry(j, r)));
end;
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);
cycle := M([[1],[2],[4],[5],[3],[7],[8],[6]]);
cartan := M([[2],[1],[6],[7],[8],[3],[4],[5]]);
t := cartan * (s * cycle);
for i in [1..8] do
  Print("TROW ", i, " ");
  for j in [1..8] do
    if t[i][j] <> Zero(F) then Print(j); fi;
    if j < 8 then Print(","); fi;
  od;
  Print("\n");
od;
QUIT;
