# determinant_holonomy_group.gap
# Holonomy group over the determinant line bundle

LoadPackage("polycyclic");

# Define the fundamental group or the base space holonomy
F := FreeGroup(2);
generators := GeneratorsOfGroup(F);

# Define a representation for the holonomy of the connection
# The holonomy group for a line bundle is U(1), but we approximate it
# using a finite cyclic group or a polycyclic group for symbolic computation.

# Let's consider a cyclic group representing roots of unity
n := 12; # Approximation
HolonomyGroup := CyclicGroup(n);
h := GeneratorsOfGroup(HolonomyGroup)[1];

# The holonomy mapping
# For a loop gamma, hol(gamma) in U(1)
HolonomyMap := GroupHomomorphismByImages(F, HolonomyGroup, generators, [h, h^2]);

# Topological anomaly obstruction
# Corresponds to the first Chern class of the determinant line bundle
# We can check if the holonomy is trivial (i.e. connection is flat)
IsTrivialHolonomy := function(hol_map)
    local img;
    img := Image(hol_map);
    return Size(img) = 1;
end;

Print("Holonomy Group: ", HolonomyGroup, "\n");
Print("Is trivial holonomy (anomaly free): ", IsTrivialHolonomy(HolonomyMap), "\n");
