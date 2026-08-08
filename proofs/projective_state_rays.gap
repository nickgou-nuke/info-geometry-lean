# projective_state_rays.gap
# Formulating discrete projective group actions over unnormalized state rays.

Print("GAP: Projective group actions over unnormalized state rays\n");

# Define a finite field and a vector space
F := GaloisField(13);
V := VectorSpace(F, 4);

# The projective space quotients out the non-zero scalars (normalization factors)
# Thus, unnormalized state rays are identified with points in the projective space.
G := PGL(4, F);

Print("The group PGL(4, F) acts on the projective space, demonstrating how scaling factors (normalization) quotient out symmetrically.\n");

# Example: Orbit size
size := Size(G);
Print("Order of the projective linear group: ", size, "\n");
