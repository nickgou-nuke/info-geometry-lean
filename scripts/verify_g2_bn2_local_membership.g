# GAP CAS gate for the local BN2 subgroup membership facts.
# The six matrices below are the fixed Lean-aligned carrier generators.
# No PC isomorphism or coordinate expansion is used here.
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
c := PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F) *
     PermutationMat((3,4,5)(6,7,8), 8, F);
t := s * c;

Hs := Group(pcgens{[1,3,4,5,6]});
Ht := Group(pcgens{[2..6]});
if Size(B) <> 64 or Size(Hs) <> 32 or Size(Ht) <> 32 then
  Error("LOCAL_SUBGROUP_SIZES failed");
fi;
if Index(B,Hs) <> 2 or Index(B,Ht) <> 2 then
  Error("LOCAL_SUBGROUP_INDICES failed");
fi;
if Intersection(B,B^s) <> Hs or Intersection(B,B^t) <> Ht then
  Error("LOCAL_INTERSECTIONS failed");
fi;
if not ForAll([1,3,4,5,6], i -> s^-1 * pcgens[i] * s in B) then
  Error("S_COMPLEMENT_CONJUGATION failed");
fi;
if not ForAll([2..6], i -> t^-1 * pcgens[i] * t in B) then
  Error("T_COMPLEMENT_CONJUGATION failed");
fi;
Print("LOCAL_SUBGROUP_SIZES=PASS\n");
Print("LOCAL_SUBGROUP_INDICES=PASS\n");
Print("LOCAL_INTERSECTIONS=PASS\n");
Print("S_COMPLEMENT_CONJUGATION=PASS\n");
Print("T_COMPLEMENT_CONJUGATION=PASS\n");
Print("NO_PC_ISOMORPHISM_DEPENDENCE=PASS\n");
QUIT;
