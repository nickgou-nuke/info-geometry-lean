# Bidirectional Schreier factorisations between the fixed CAS carrier and the
# exact Lean-aligned generators. The emitted words are transport artifacts.

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

pc := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];;
leanWeyl := [
  M([[1],[2],[4],[3],[5],[7],[6],[8]]),
  M([[2],[1],[8],[7],[6],[5],[4],[3]])
];;
lean := Concatenation(pc, leanWeyl);;

codes := [
  [2,1,128,64,32,16,8,4],
  [2,1,128,192,224,24,12,4],
  [134,133,128,68,175,211,136,4],
  [1,2,4,8,24,32,192,128],
  [129,130,4,8,147,40,68,128],
  [2,1,64,32,128,8,4,16]
];;
cas := List(codes, c -> List([1..8], i ->
  List([1..8], j -> ((Int(c[j] / 2^(i-1)) mod 2) * One(F)))));;
G := Group(cas);;
L := Group(lean);;
if Size(G) <> 12096 or Size(L) <> 12096 then Error("ALIGNMENT_GROUP_SIZE_FAIL"); fi;;

for i in [1..Length(cas)] do
  Print("CAS_TO_LEAN_", i-1, "=", Factorization(L, cas[i]), "\n");
od;;
for i in [1..Length(lean)] do
  Print("LEAN_TO_CAS_", i-1, "=", Factorization(G, lean[i]), "\n");
od;;
Print("BIDIRECTIONAL_GENERATOR_ALIGNMENT_CAS=PASS\n");
QUIT;
