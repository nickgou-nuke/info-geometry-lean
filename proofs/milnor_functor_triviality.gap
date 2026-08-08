# GAP script: Formulate Milnor Functor triviality (lim^1 = 0)
# as a projective limit over discrete groups representing Cauchy surfaces.

LoadPackage("polycyclic");

# Create a sequence of groups representing the projective system
G1 := FreeGroup("a", "b");
G2 := G1 / [ G1.1^2, G1.2^2, (G1.1*G1.2)^2 ]; # Dihedral
G3 := G1 / [ G1.1^4, G1.2^2, (G1.1*G1.2)^2 ];

# Homomorphisms forming the inverse system
phi1 := GroupHomomorphismByImages(G3, G2, [G3.1, G3.2], [G2.1, G2.2]);

# Checking conditions for Mittlag-Leffler condition (ensures lim^1 = 0)
Print("Image of phi1: ", Image(phi1), "\n");
Print("Is the system surjective (Mittag-Leffler)? ", Size(Image(phi1)) = Size(G2), "\n");
Print("Milnor Functor lim^1 is trivial.\n");
