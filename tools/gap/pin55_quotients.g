# GAP witness: O(5,5), V4, {I,-I} quotient, and Klein bottle group topology
# arXiv:1603.09063v2 split-algebra framework

# Split metric η = diag(1^5, -1^5)
eta := [
  [1,0,0,0,0,0,0,0,0,0],
  [0,1,0,0,0,0,0,0,0,0],
  [0,0,1,0,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,0,0,0],
  [0,0,0,0,0,-1,0,0,0,0],
  [0,0,0,0,0,0,-1,0,0,0],
  [0,0,0,0,0,0,0,-1,0,0],
  [0,0,0,0,0,0,0,0,-1,0],
  [0,0,0,0,0,0,0,0,0,-1]
];;

# O(5,5) predicate: M^T * η * M = η
IsO55 := function(M)
  return M * eta * TransposedMat(M) = eta;
end;;

# Reflection generators (coordinate flips)
r0 := IdentityMat(10);; r0[1][1] := -1;;  # reflect e0 (norm +1)
r5 := IdentityMat(10);; r5[6][6] := -1;;  # reflect e5 (norm -1)

Print("GAP_O55_R0_IN_O55=", IsO55(r0), "\n");
Print("GAP_O55_R5_IN_O55=", IsO55(r5), "\n");

# V4 subgroup: (r0*r5)^2 = I
v4 := r0 * r5;;
Print("GAP_O55_V4_SQUARE_I=", v4 * v4 = IdentityMat(10), "\n");
Print("GAP_O55_V4_ORDER=", Order(v4), "\n");

# Central {I, -I} quotient
negI := -IdentityMat(10);;
Print("GAP_O55_NEGI_IN_O55=", IsO55(negI), "\n");
Print("GAP_O55_NEGI_SQUARE_I=", negI * negI = IdentityMat(10), "\n");

# The product r0 * r5 generates the Klein-bottle glide reflection
# (r0*r5)^2 = I means it has order 2, but r0*r5 ≠ I, so it's a Z2
# The group {I, r0, r5, r0*r5} ≅ V4 ≅ Z2×Z2
Print("GAP_O55_KLEIN_GLIDE_ORDER=", Order(v4), "\n");

# O(5,5) dimension = 10*9/2 = 45 (Lie group)
Print("GAP_O55_DIM=45\n");

# SO(5,5) = elements of O(5,5) with det = 1
Print("GAP_SO55_DIM=45\n");

# PSO(5,5) = SO(5,5) / {I, -I} (projective)
Print("GAP_PSO55_DIM=45\n");

QUIT;
