# CAS derivation of the concrete flag action G/B.
#
# This is a Schreier/coset-action certificate, not a carrier enumeration:
# GAP constructs the action on right cosets of B and records the six
# generator transitions.  It is intended as input to a later native Lean
# orbit/stabilizer proof; it is not itself a Lean theorem.

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
B := SylowSubgroup(G, 2);
Q := RightCosets(G, B);
if Length(Q) <> 189 then Error("FLAG_CARD failed"); fi;

# Choose the two simple-reflection representatives from the concrete carrier.
# The predicates are intrinsic to G and B: each reflection extends B to a
# rank-one subgroup of order 192, and their product has Coxeter order 6.
s := First(Elements(G), g -> Order(g) = 2 and
  Size(ClosureGroup(B, g)) = 192);
t := First(Elements(G), g -> Order(g) = 2 and
  Size(ClosureGroup(B, g)) = 192 and Order(s * g) = 6);
if s = fail or t = fail then Error("WEYL_GENERATORS failed"); fi;
if Order(s) <> 2 or Order(t) <> 2 or Order(s * t) <> 6 then
  Error("WEYL_RELATIONS failed");
fi;

# The action degree is the concrete index [G:B].  The first coset is the
# canonical base flag, and its stabilizer is B by the coset action theorem.
act := ActionHomomorphism(G, Q, OnRight);
if Length(Q) <> 189 then Error("FLAG_ACTION_DEGREE failed"); fi;
A := Image(act);
Print("FLAG_ACTION_READY\n");
if Size(Stabilizer(A, 1)) <> 64 then Error("FLAG_STABILIZER failed"); fi;
Print("FLAG_STABILIZER_SIZE=", Size(Stabilizer(A, 1)), "\n");
if not IsTransitive(A) then Error("FLAG_TRANSITIVITY failed"); fi;
Print("FLAG_ACTION_TRANSITIVE=PASS\n");

# The twelve Bruhat cells on G/B are the B-orbits of the twelve Weyl base
# cosets.  This is the finite CAS certificate consumed by the Lean transport.
Wwords := [
  [], [s], [t], [s,t], [t,s], [s,t,s], [t,s,t],
  [s,t,s,t], [t,s,t,s], [s,t,s,t,s], [t,s,t,s,t],
  [s,t,s,t,s,t]
];
Wmats := List(Wwords, w -> Product(Concatenation([s^0], w)));
Bact := Image(act, B);
cells := [];
for w in Wmats do
  base := PositionProperty(Q, q -> Representative(q) = w);
  if base = fail then Error("WEYL_BASE_COSET failed"); fi;
  Add(cells, Orbit(Bact, base));
od;
allCells := Union(cells);
if Length(allCells) <> 189 or Sum(cells, Length) <> 189 then
  Error("BRUHAT_CELL_PARTITION failed");
fi;
Print("BRUHAT_CELL_SIZES=", List(cells, Length), "\n");
Print("BRUHAT_CELL_PARTITION=PASS\n");

# Export the exact finite cell membership arrays in zero-based Lean indices.
for k in [1..Length(cells)] do
  Print("FLAG_CELL_", k-1, "=", SortedList(List(cells[k], i -> i-1)), "\n");
od;

# Export the actual action images.  These are GAP-derived permutations on the
# 189 right cosets; no Lean-side relation is assumed here.
for k in [1..Length(gens)] do
  Print("FLAG_PERM_", k-1, "=",
    List([1..Length(Q)], i -> i^Image(act, gens[k])), "\n");
od;

Print("FLAG_ACTION_DEGREE=", Length(Q), "\n");
Print("FLAG_STABILIZER_SIZE=", Size(Stabilizer(A, 1)), "\n");
Print("FLAG_ACTION_TRANSITIVE=PASS\n");
Print("G2_FLAG_COSET_ACTION_CAS=PASS\n");
QUIT;
