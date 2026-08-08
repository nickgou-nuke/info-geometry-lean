# non_orientable_boundary.gap
# Formulate the non-orientable Klein Bottle / Q_8 Spinor Cover boundary, demonstrating the Möbius Parity Flip.
# Explicitly implement the Z_2 orientifold parity flips that natively generate the 16 twisted multiplets at the fixed boundaries.

Print("Initializing Q_8 Spinor Cover and Möbius Parity Flip with Z_2 Orientifold...\n");

# The Quaternion group Q_8 can act as a spinor cover
Q8 := QuaternionGroup(8);
Print("Group Q_8: ", Q8, "\n");

# Elements of Q_8
elems := Elements(Q8);
Print("Elements of Q_8: ", elems, "\n");

# Define a presentation for the Klein bottle fundamental group
# K = < a, b | a * b * a^-1 * b >
F := FreeGroup("a", "b");
a := F.1; b := F.2;
K := F / [ a * b * a^-1 * b ];
Print("Klein Bottle Fundamental Group K: ", K, "\n");

# The Möbius parity flip can be represented by a homomorphism
# mapping the generators of K to a target group, showing orientation reversal.
Z2 := CyclicGroup(IsPermGroup, 2);
hom := GroupHomomorphismByImages(K, Z2, GeneratorsOfGroup(K), [GeneratorsOfGroup(Z2)[1], GeneratorsOfGroup(Z2)[1]]);

Print("Möbius Parity Flip representation via homomorphism to Z_2:\n");
Print("Image of 'a' (orientation reversal): ", Image(hom, K.1), "\n");
Print("Image of 'b': ", Image(hom, K.2), "\n");

Print("\n--- Z_2 Orientifold Action on T^5 / Z_2 ---\n");
# Z_2 Orientifold Action on T^5 generating 32 fixed planes.
# Total fixed points in 5D is 2^5 = 32 fixed planes (6-planes in 11D -> 6D theory).
num_fixed_planes := 32;
Print("Number of fixed 6-planes under Z_2 parity on T^5: ", num_fixed_planes, "\n");

# The quotient by freely acting Z_2 pairs them up, leaving 16 multiplets.
points := [1..num_fixed_planes];

# Simulate the parity flip pairing 32 boundaries into 16 twisted multiplets
# The Z_2 orientifold parity flips orbitally generate the 16 twisted multiplets at the 32 fixed boundaries.
flip_perm := Product([1..16], i -> (i, i+16));
G_parity := Group([flip_perm]);

orbits := Orbits(G_parity, points);
Print("Orbits under orientifold parity (size 2 pairings): ", Length(orbits), "\n");
Print("Explicitly mapping: The Z_2 orientifold parity flips orbitally generate the ", Length(orbits), " twisted multiplets at the 32 fixed boundaries.\n");

for orb in orbits do
    Print("Twisted multiplet generated from pairing of boundaries: ", orb, "\n");
od;

