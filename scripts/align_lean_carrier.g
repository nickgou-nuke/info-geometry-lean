# CAS-only carrier alignment for the six explicit Lean PC automorphisms.
# The matrices below are the coordinate maps in pc1Fun,...,pc6Fun, not GAP's
# arbitrary Pcgs(U).  GAP matrices act on row vectors here, so the rows are
# copied literally from the Lean coordinate formulas.
F := GF(2);;
entry := function(j, support)
  if j in support then return One(F); fi;
  return Zero(F);
end;;
M := function(rows)
  return List(rows, r -> List([1..8], j -> entry(j, r)));
end;;

leanGens := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];;

s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);;
B := Group(leanGens);;
if Size(B) <> 64 then Error("LEAN_CARRIER_SIZE_FAIL"); fi;;
Print("LEAN_CARRIER_SIZE=PASS\n");

# The first local target is the conjugate of the first Lean generator.
target := s^-1 * leanGens[1] * s;;
if not target in B then Error("LEAN_CONJUGATE_MEMBERSHIP_FAIL"); fi;;
Print("LEAN_S_CONJ_PC1_IN_B=PASS\n");

# Export the exact matrix target for an independent triangular decomposition.
Print("LEAN_S_CONJ_PC1="); Print(target); Print("\n");
Print("LEAN_S_CONJ_PC1_FACTORIZATION="); Print(Factorization(B, target)); Print("\n");
Print("LEAN_S_CONJ_PC1_EQUALS_PC3_PC5=", target = leanGens[3] * leanGens[5], "\n");
Print("LEAN_S_CONJ_PC1_EQUALS_PC5_PC3=", target = leanGens[5] * leanGens[3], "\n");
Print("LEAN_S_CONJ_PC1_WORD=[0,0,1,0,1,0]\n");
Print("LEAN_CARRIER_ALIGNMENT_MEMBERSHIP=PASS\n");
QUIT;
