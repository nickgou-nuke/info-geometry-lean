# Probe which Lean-composition-order t preserves the fixed PC carrier.
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
pcgens := List(rows, rs -> List([1..8], i -> List([1..8], j -> entry(j, rs[i]))));
B := Group(pcgens);
s := PermutationMat((3,4)(6,7), 8, F);
c := PermutationMat((3,4,5)(6,7,8), 8, F) *
     PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F);
t := cycle * (s * cartan);
Print("T_LEAN_ORDER_T_ORDER=", Order(t), "\n");
Print("T_LEAN_ORDER_INTERSECTION_INVERSE_SIZE=", Size(Intersection(B, B^(t^-1))), "\n");
H := Intersection(B, B^t);
Print("T_LEAN_ORDER_INTERSECTION_SIZE=", Size(H), "\n");
Print("T_LEAN_ORDER_INTERSECTION_GENERATORS="); Print(GeneratorsOfGroup(H)); Print("\n");
Print("T_LEAN_ORDER_SIZE=", Size(Group(pcgens)), "\n");
for i in [1..6] do
  Print("T_LEAN_ORDER_CONJ_P", i-1, "_IN_B=", t * pcgens[i] * t in B, "\n");
od;
QUIT;
