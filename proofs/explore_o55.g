# GAP Script: Exploring the split orthogonal group O+(10, q) 
# This serves as the finite algebraic proxy for the continuous O(5,5)

Print("--- Structural Exploration of O(5,5) via GAP ---\n");

# We analyze the finite split orthogonal group GO+(10, q)
# The split signature (+1) over dimension 10 gives the exact structural
# root system (D5) as the continuous pseudo-Riemannian O(5,5).
q := 3;;
G := GO( +1, 10, q );;

Print("Group G = GO+(10, ", q, ") (Proxy for O(5,5))\n");
Print("Order of G: ", Size(G), "\n");

# The commutator subgroup is Omega+(10, q), which corresponds to the connected component SO+(5,5)
OmegaSub := DerivedSubgroup(G);;
Print("Order of Derived Subgroup Omega+(10, ", q, "): ", Size(OmegaSub), "\n");
Print("Index [G : Omega]: ", Index(G, OmegaSub), " (representing the reflection components / Pin covering)\n");

# Let's look at the center of the group
C := Center(G);;
Print("Order of the Center Z(G): ", Size(C), "\n");

# We can also compute the Lie algebra of type D5 over GF(q)
L := SimpleLieAlgebra("D", 5, GF(q));;
Print("\n--- Lie Algebra D5 (so(5,5)) ---\n");
Print("Dimension of so(5,5): ", Dimension(L), "\n");

# Roots and Cartan Subalgebra for type D5: |Φ(D_n)| = 2*n*(n-1), rank = n
Print("Number of Roots (Positive + Negative): ", 2*5*(5-1), "\n");
Print("Rank of Cartan Subalgebra: ", 5, "\n");

# We output the structure of the Cartan Matrix of D5
cm := [[2,-1,0,0,0],[-1,2,-1,0,0],[0,-1,2,-1,-1],[0,0,-1,2,0],[0,0,-1,0,2]];;
Print("Cartan Matrix of D5:\n");
for row in cm do
    Print(row, "\n");
od;

QUIT;
