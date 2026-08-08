# orientation_sheaf_group.gap
# Structure group of the pseudo-orthogonal frame bundle and associated bundle sections

Print("Defining orientation sheaf group structure\n");

# For O(p,q), the component group is Z/2Z x Z/2Z
# We represent the characters as homomorphisms from this component group

DeclareOperation("OrientationSheafGroup", [IsInt, IsInt]);

InstallMethod(OrientationSheafGroup,
    "for two integers (p, q)",
    [IsInt, IsInt],
    function(p, q)
        local G, sigma_plus, sigma_minus, sigma;
        
        # The component group is V4 (Klein four-group)
        G := Group((1,2), (3,4)); 
        
        # Space orientation character
        sigma_plus := GroupHomomorphismByImages(G, Group((1,2)), [(1,2), (3,4)], [(1,2), ()]);
        
        # Time orientation character
        sigma_minus := GroupHomomorphismByImages(G, Group((1,2)), [(1,2), (3,4)], [(), (1,2)]);
        
        # Determinant character
        sigma := GroupHomomorphismByImages(G, Group((1,2)), [(1,2), (3,4)], [(1,2), (1,2)]);
        
        return rec(
            group := G,
            space_char := sigma_plus,
            time_char := sigma_minus,
            det_char := sigma
        );
    end
);

Print("Orientation sheaf group formulation loaded.\n");
