# pin55_weyl_group.gap
# Weyl group of Pin(5,5) acting on Cartan Subalgebra.
# Pin(5,5) has Lie algebra of type D5.

Print("Formulating the Weyl group of Pin(5,5) acting on the Cartan Subalgebra...\n");

# Define the simple Lie algebra of type D5 over Rationals
L := SimpleLieAlgebra("D", 5, Rationals);

# Get the root system and the corresponding Weyl group
R := RootSystem(L);
W := WeylGroup(R);

Print("The Weyl group of Pin(5,5) is of type D5.\n");
Print("Order of the Weyl group: ", Size(W), "\n");
