# Unitary group symmetries preserving the Re(s) = 1/2 axis
# under the Mobius parity flip.

Print("Initializing Critical Line Group in GAP\n");

# We consider a finite analogue of the Unitary Group U(2, q)
# that acts on the 2D space where the critical line symmetry is modeled.
q := 5; # A prime power for our finite field
G := GU(2, q);

Print("Group GU(2, 5) generated.\n");
Print("Size of G: ", Size(G), "\n");

# The Mobius parity flip operator acts as an involution.
# Let's find involutions in the center or related normal subgroups.
Z := Center(G);
involutions := Filtered(Elements(G), g -> Order(g) = 2);

Print("Number of involutions (potential Mobius parity flips): ", Size(involutions), "\n");

# Select a canonical Mobius parity flip (e.g., the central involution)
mobius_flip := First(involutions, i -> i in Z);
if mobius_flip = fail then
    mobius_flip := involutions[1];
fi;

Print("Mobius Parity Flip chosen: ", mobius_flip, "\n");

# The symmetry group preserving the Re(s) = 1/2 axis
# corresponds to the centralizer of the Mobius parity flip.
critical_line_symmetry_group := Centralizer(G, mobius_flip);

Print("Size of Critical Line Symmetry Group (Centralizer of Mobius flip): ", Size(critical_line_symmetry_group), "\n");

# Output the structure of the critical line symmetry group
Print("Structure Description: ", StructureDescription(critical_line_symmetry_group), "\n");
