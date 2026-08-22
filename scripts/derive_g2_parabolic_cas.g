# CAS derivation of the genuine maximal parabolic containing the concrete
# Sylow-2 subgroup.  This is deliberately separate from N_G(U), which is U.

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
if Size(Normalizer(G, U)) <> 64 then Error("U_NORMALIZER failed"); fi;

maximals := MaximalSubgroups(G);
parabolics := Filtered(maximals, P -> Size(P) = 192 and IsSubgroup(P, U));
if Length(parabolics) = 0 then Error("PARABOLIC_NOT_FOUND"); fi;
P := parabolics[1];

if not IsSubgroup(P, U) then Error("U_NOT_SUBGROUP_OF_P"); fi;
if Index(G, P) <> 63 then Error("PARABOLIC_INDEX failed"); fi;
if Index(P, U) <> 3 then Error("PARABOLIC_FIBER failed"); fi;

Pshort := Group(Concatenation(pcgens, [s]));
Plong := Group(Concatenation(pcgens, [t]));
if not (Size(Pshort) = 192 or Size(Plong) = 192) then
  Error("SIMPLE_PARABOLIC_GENERATOR failed");
fi;

Q := RightCosets(G, P);
A := Action(G, Q, OnRight);
if Length(Q) <> 63 then Error("PARABOLIC_ACTION_DEGREE failed"); fi;
if Size(Stabilizer(A, 1)) <> 192 then Error("PARABOLIC_ACTION_STABILIZER failed"); fi;
if Transitivity(A) <> 1 then Error("PARABOLIC_ACTION_TRANSITIVE failed"); fi;

parabolicCells := Orbits(U, Q, OnRight);
cellSizes := SortedList(List(parabolicCells, Length));
if cellSizes <> [1,2,4,8,16,32] then
  Error("PARABOLIC_SCHUBERT_SIZES failed");
fi;
if Sum(cellSizes) <> 63 then Error("PARABOLIC_SCHUBERT_COVER failed"); fi;

Print("G_SIZE=", Size(G), "\n");
Print("U_SIZE=", Size(U), "\n");
Print("NORMALIZER_U_SIZE=", Size(Normalizer(G, U)), "\n");
Print("P_SIZE=", Size(P), "\n");
Print("G_OVER_P=", Index(G, P), "\n");
Print("P_OVER_U=", Index(P, U), "\n");
Print("P_SHORT_SIZE=", Size(Pshort), "\n");
Print("P_LONG_SIZE=", Size(Plong), "\n");
Print("PARABOLIC_ACTION_DEGREE=", Length(Q), "\n");
Print("PARABOLIC_STABILIZER_SIZE=", Size(Stabilizer(A, 1)), "\n");
Print("PARABOLIC_SCHUBERT_SIZES=", cellSizes, "\n");
Print("G2_PARABOLIC_CAS=PASS\n");
QUIT;
