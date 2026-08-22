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

# The action degree is the concrete index [G:B].  The first coset is the
# canonical base flag, and its stabilizer is B by the coset action theorem.
A := Action(G, Q, OnRight);
act := ActionHomomorphism(G, Q, OnRight);
if NrMovedPoints(A) <> 189 then Error("FLAG_ACTION_DEGREE failed"); fi;
if Size(Stabilizer(A, 1)) <> 64 then Error("FLAG_STABILIZER failed"); fi;
if Transitivity(A) <> 1 then Error("FLAG_TRANSITIVITY failed"); fi;

# Export the actual action images.  These are GAP-derived permutations on the
# 189 right cosets; no Lean-side relation is assumed here.
for k in [1..Length(gens)] do
  Print("FLAG_PERM_", k-1, "=",
    List([1..Length(Q)], i -> i^Image(act, gens[k])), "\n");
od;

Print("FLAG_ACTION_DEGREE=", NrMovedPoints(A), "\n");
Print("FLAG_STABILIZER_SIZE=", Size(Stabilizer(A, 1)), "\n");
Print("FLAG_ACTION_TRANSITIVE=PASS\n");
Print("G2_FLAG_COSET_ACTION_CAS=PASS\n");
QUIT;
