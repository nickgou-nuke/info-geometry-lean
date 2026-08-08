# GAP script for analyzing permutation groups acting on perfect matchings of bipartite graphs
LoadPackage("grape");

BipartiteMatchingGroup := function(n)
    local G, V, E, bg, matchings, S_n, action, i, j;
    
    # Define the symmetric group acting on rows and columns
    S_n := SymmetricGroup(n);
    
    # We can represent perfect matchings as permutations
    # The action of S_n x S_n on perfect matchings (permutations)
    # can be described as follows: for a matching sigma,
    # (pi_row, pi_col) * sigma = pi_col^-1 * sigma * pi_row
    
    Print("Defined symmetric group of degree ", n, " for bipartite matchings.\n");
    return S_n;
end;

n := 4;
G := BipartiteMatchingGroup(n);
matchings := Elements(SymmetricGroup(n));
Print("Number of perfect matchings (permutation matrices) for n=", n, ": ", Length(matchings), "\n");

# Show basic permutation matrices properties
Print("Permutation matrix representations can be built from these permutations.\n");
