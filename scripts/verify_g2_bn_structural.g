# Structural GAP gate for the concrete BN/Bruhat data.
# It uses GAP's matrix-group and double-coset algorithms; it does not
# enumerate the carrier, the 64-element subgroup, or pairs of carrier elements.

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
B := Group(pcgens);

s := PermutationMat((3,4)(6,7), 8, F);
r := PermutationMat((3,4,5)(6,7,8), 8, F);
h := PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F);
c := h*r;
N := Group(s,c);
G := Group(Concatenation(pcgens, [s,r,h]));

if Size(G) <> 12096 then Error("G_SIZE failed"); fi;
if Size(B) <> 64 then Error("B_SIZE failed"); fi;
if Size(N) <> 12 then Error("N_SIZE failed"); fi;
if Size(Intersection(B,N)) <> 1 then Error("BN_INTERSECTION failed"); fi;
intersectionSizes := List(Elements(N), n -> Size(Intersection(B, B^n)));
if Set(intersectionSizes) <> [1,2,4,8,16,32,64] then
  Error("INTERSECTION_SIZE_PROFILE failed");
fi;
if Size(Intersection(B, B^s)) <> 32 then
  Error("SIMPLE_REFLECTION_INTERSECTION failed");
fi;

dcs := DoubleCosetRepsAndSizes(G, B, B);
if Length(dcs) <> 12 then Error("DOUBLE_COSET_COUNT failed"); fi;
if not ForAll(dcs, x -> ForAny(Elements(N), n ->
    x[1] in DoubleCoset(B, n, B))) then
  Error("N_REPRESENTS_ALL_DOUBLE_COSETS failed");
fi;

sizes := List(dcs, x -> x[2]);
if Sum(sizes) <> 12096 then Error("DOUBLE_COSET_SUM failed"); fi;
if Set(List(sizes, x -> x / 64)) <> [1,2,4,8,16,32,64] then
  Error("DOUBLE_COSET_WEIGHTS failed");
fi;

Print("G_SIZE=PASS\n");
Print("B_SIZE=PASS\n");
Print("N_SIZE=PASS\n");
Print("BN_INTERSECTION=PASS\n");
Print("INTERSECTION_SIZE_PROFILE=PASS\n");
Print("SIMPLE_REFLECTION_INTERSECTION=PASS\n");
Print("DOUBLE_COSET_COUNT=PASS\n");
Print("N_REPRESENTS_ALL_DOUBLE_COSETS=PASS\n");
Print("DOUBLE_COSET_SUM=PASS\n");
Print("DOUBLE_COSET_WEIGHTS=PASS\n");
QUIT;
