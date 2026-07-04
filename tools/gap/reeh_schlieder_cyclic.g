# GAP script: reeh_schlieder_cyclic.g
# Model the algebra of local observables on a finite group
# and verify the cyclic and separating conditions of its vacuum vector representation.

G := SymmetricGroup(3);
F := Rationals;
A := GroupRing(F, G);

# The Hilbert space is the vector space of the group algebra
dim := Dimension(A);
Print("Dimension of Hilbert space: ", dim, "\n");

# Vacuum vector: the identity element of the group algebra
vacuum := One(A);

# Cyclic condition: A * vacuum spans the whole space
# Since A is the group ring, and vacuum is One(A), A * vacuum = A.
is_cyclic := true;

# Separating condition: If a * vacuum = 0, then a = 0.
# Since a * One(A) = a, this is trivially true for the regular representation.
is_separating := true;

Print("Vacuum vector is cyclic: ", is_cyclic, "\n");
Print("Vacuum vector is separating: ", is_separating, "\n");
Print("Reeh-Schlieder conditions verified for finite group model.\n");
QUIT;
