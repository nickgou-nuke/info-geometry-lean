# GAP finite witness for the reduced-structure split-complex boundary.
# We model the signed split-complex basis-unit shadow by the Klein four group on
# four labels via two commuting involutions. This is a finite shadow only; it is
# not a proof of any global reduced-structure group or spin-group isomorphism.

signFlip := (1,2)(3,4);;
jFlip := (1,3)(2,4);;
G := Group(signFlip, jFlip);;
Print("GAP_REDUCED_STRUCTURE_SIGNED_SPLIT_COMPLEX_SIZE=", Size(G), "\n");
Print("GAP_REDUCED_STRUCTURE_SIGNED_SPLIT_COMPLEX_ID=", IdGroup(G), "\n");
Print("GAP_REDUCED_STRUCTURE_SIGNED_SPLIT_COMPLEX_IS_ABELIAN=", IsAbelian(G), "\n");
QUIT;
