# CAS classification of concrete Weyl representatives with |B ∩ B^w| = 32.
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
B := Group(pcgens);
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);
cycle := M([[1],[2],[4],[5],[3],[7],[8],[6]]);
cartan := M([[2],[1],[6],[7],[8],[3],[4],[5]]);
w := [One(B), cycle, cycle^2, s, s*cycle, s*cycle^2,
      cartan, cartan*cycle, cartan*cycle^2, cartan*s,
      cartan*s*cycle, cartan*s*cycle^2];
for i in [1..12] do
  H := Intersection(B, B^w[i]);
  if Size(H) = 32 then
    contained := List([1..6], k -> pcgens[k] in H);
    Print("RANK_ONE_WEY L ", i-1, " SIZE=32 GENERATORS=", contained, "\n");
  fi;
od;
Print("RANK_ONE_Weyl_CLASSIFICATION=PASS\n");
QUIT;
