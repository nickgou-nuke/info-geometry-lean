LoadPackage("repn");
G := SU(3, 5); # Finite approximation for color group
S2 := SylowSubgroup(G, 2); # SU(2) instanton embedding

# Sequential minimization over SU(2) subgroups (Cooling procedure from paper)
cooling_subgroups := ConjugacyClassesSubgroups(G);
su2_embeddings := Filtered(cooling_subgroups, c -> Size(Representative(c)) = 120);

# The instanton-anti-instanton interaction alignment
Print("SU(2) embeddings inside SU(3) for cooling: ", Length(su2_embeddings), "\n");
