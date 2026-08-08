# GAP Script: Orbifold Discrete Torsion for T^5 / Z_2
Print("Computing discrete torsion for T^5 / Z_2 twisted sectors...\n");

# Define the orbifold group Gamma = Z_2
Gamma := Group((1,2));

# In a T^5 / Z_2 orbifold, there are 2^5 = 32 fixed points.
# We are interested in the discrete torsion phases in the group algebra.
# Discrete torsion corresponds to H^2(Gamma, U(1)).
# For Gamma = Z_2, H^2(Z_2, U(1)) is trivial, but if we consider multiple actions,
# say Z_2 x Z_2, we can have non-trivial torsion.
# Let's consider a generic multi-Z2 for full T-duality phase structure.

G := DirectProduct(Group((1,2)), Group((3,4))); 
Print("Group considered: ", StructureDescription(G), "\n");

# The Schur Multiplier (H^2(G, C*)) gives the possible discrete torsion.
# For Z2 x Z2, it is Z2.
mult := AbelianInvariantsMultiplier(G);
Print("Abelian Invariants of the Schur Multiplier (Discrete Torsion): ", mult, "\n");

if Length(mult) > 0 then
    Print("Non-trivial discrete torsion is present.\n");
else
    Print("Trivial discrete torsion for this specific group.\n");
fi;
