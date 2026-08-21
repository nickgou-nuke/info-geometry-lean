# Concrete carrier-level BN/Bruhat audit for SplitOctF2Aut.
#
# This is a CAS certificate only.  It deliberately uses GAP's
# DoubleCosets operation; it does not enumerate B x w x B in Python and it
# does not turn the resulting order arithmetic into a Lean theorem.

F := GF(2);
codes := [
  [2,1,128,64,32,16,8,4],
  [2,1,128,192,224,24,12,4],
  [134,133,128,68,175,211,136,4],
  [1,2,4,8,24,32,192,128],
  [129,130,4,8,147,40,68,128],
  [2,1,64,32,128,8,4,16]
];
gens := List(codes, c -> List([1..8], i ->
  List([1..8], j -> ((Int(c[j] / 2^(i-1)) mod 2) * One(F)))));
G := Group(gens);
if Size(G) <> 12096 then Error("carrier group order is not 12096"); fi;
B := SylowSubgroup(G, 2);
if Size(B) <> 64 then Error("Sylow 2 subgroup order is not 64"); fi;

# Weyl representatives: the concrete A2 permutations together with the
# Cartan swap.  These are the same carrier matrices used by the native
# generator owners, expressed here independently in GAP.
weylRows := [
  [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],
   [0,0,0,1,0,0,0,0],[0,0,1,0,0,0,0,0],
   [0,0,0,0,1,0,0,0],[0,0,0,0,0,0,1,0],
   [0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,1]],
  [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],
   [0,0,0,0,1,0,0,0],[0,0,1,0,0,0,0,0],
   [0,0,0,1,0,0,0,0],[0,0,0,0,0,0,0,1],
   [0,0,0,0,0,1,0,0],[0,0,0,0,0,0,1,0]],
  [[0,1,0,0,0,0,0,0],[1,0,0,0,0,0,0,0],
   [0,0,0,0,0,1,0,0],[0,0,0,0,0,0,1,0],
   [0,0,0,0,0,0,0,1],[0,0,1,0,0,0,0,0],
   [0,0,0,1,0,0,0,0],[0,0,0,0,1,0,0,0]]
];
weyl := List(weylRows, rows -> List(rows, row ->
  List(row, x -> x * One(F))));
N := Group(weyl);
if Size(N) <> 12 then Error("concrete Weyl subgroup order is not 12"); fi;
if Size(Intersection(B, N)) <> 1 then Error("B intersect N is not trivial"); fi;

cells := DoubleCosets(G, B, B);
if Length(cells) <> 12 then Error("number of concrete double cosets is not 12"); fi;
if Sum(List(cells, Size)) <> Size(G) then
  Error("concrete double cosets do not cover the carrier");
fi;

# Every double coset has a representative in the concrete Weyl subgroup.
# Since DoubleCosets returns disjoint double cosets, this also certifies one
# Weyl representative per cell once the intersection check above holds.
cellWeylCounts := [];
for d in cells do
  count := Number(Elements(N), n -> n in d);
  Add(cellWeylCounts, count);
  if count <> 1 then Error("cell does not have a unique Weyl representative"); fi;
od;

Print("carrier_group_size=", Size(G), "\n");
Print("borel_sylow_two_size=", Size(B), "\n");
Print("concrete_weyl_size=", Size(N), "\n");
Print("borel_intersect_weyl_size=", Size(Intersection(B, N)), "\n");
Print("double_coset_count=", Length(cells), "\n");
Print("double_coset_sizes=", List(cells, Size), "\n");
Print("double_coset_sum=", Sum(List(cells, Size)), "\n");
Print("unique_weyl_representative_counts=", cellWeylCounts, "\n");
Print("CONCRETE_BN_BRUHAT_CAS=PASS\n");
QUIT;
