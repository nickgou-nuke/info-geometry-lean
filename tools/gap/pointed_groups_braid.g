# GAP exact witness for Ross Street, "Braids among the groups".
#
# Checks Artin's braid action on the free group F3:
#   beta_i(x_i)     = x_{i+1}
#   beta_i(x_{i+1}) = x_{i+1} x_i x_{i+1}^-1
#   beta_i(x_j)     = x_j otherwise
# and verifies beta1 beta2 beta1 = beta2 beta1 beta2 on generators.
#
# This is a finite generator-level witness for the representation laws, not a
# proof of every global categorical coherence theorem in Street's paper.

RequireTrue := function(name, cond)
  if not cond then
    Error(Concatenation("[FAIL] ", name));
  fi;
  Print("[OK] ", name, "\n");
end;

F := FreeGroup("x1", "x2", "x3");;
x1 := F.1;;
x2 := F.2;;
x3 := F.3;;
gens := [x1, x2, x3];;

beta1 := GroupHomomorphismByImages(F, F, gens, [x2, x2 * x1 * x2^-1, x3]);;
beta2 := GroupHomomorphismByImages(F, F, gens, [x1, x3, x3 * x2 * x3^-1]);;

RequireTrue("beta1 is an automorphism", IsBijective(beta1));
RequireTrue("beta2 is an automorphism", IsBijective(beta2));

LHS := beta1 * beta2 * beta1;;
RHS := beta2 * beta1 * beta2;;

Print("Checking Braid Relation beta1 beta2 beta1 = beta2 beta1 beta2 on F3\n");
for x in gens do
  Print("  LHS(", x, ") = ", Image(LHS, x), "\n");
  Print("  RHS(", x, ") = ", Image(RHS, x), "\n");
  RequireTrue(Concatenation("Artin relation on ", String(x)), Image(LHS, x) = Image(RHS, x));
od;

# Coxeter/permutation quotient anchor: impose adjacent transpositions in S3.
S3 := SymmetricGroup(3);;
s1 := (1,2);;
s2 := (2,3);;
RequireTrue("S3 sigma1^2=1", s1^2 = One(S3));
RequireTrue("S3 sigma2^2=1", s2^2 = One(S3));
RequireTrue("S3 braid relation", s1 * s2 * s1 = s2 * s1 * s2);

Print("POINTED_GROUPS_BRAID_GAP_OK\n");
