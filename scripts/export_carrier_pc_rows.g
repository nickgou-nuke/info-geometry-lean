# Machine-readable CAS export for the fixed Lean PC carrier.
# No SylowSubgroup, Pcgs, or arbitrary PC isomorphism is used.
F := GF(2);;
M := function(rows)
  local m, i, j;
  m := [];
  for i in [1..8] do
    Add(m, []);
    for j in [1..8] do
      if j in rows[i] then Add(m[i], One(F));
      else Add(m[i], Zero(F)); fi;
    od;
  od;
  return m;
end;;
leanGens := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];;
if Size(Group(leanGens)) <> 64 then Error("FIXED_LEAN_PC_SIZE_FAIL"); fi;;
Print("FIXED_LEAN_PC_SIZE=PASS\n");
for i in [1..6] do
  Print("PCROW ", i, " ");
  for j in [1..8] do
    if j > 1 then Print(";"); fi;
    support := Filtered([1..8], k -> leanGens[i][j][k] <> Zero(F));
    for k in [1..Length(support)] do
      if k > 1 then Print(","); fi;
      Print(support[k]);
    od;
  od;
  Print("\n");
od;
QUIT;
