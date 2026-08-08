# conformal_parity_group.gap
Print("Formulating Parity Operators as Discrete Group Actions...\n");

F := FreeGroup("n_plus", "n_minus", "s_plus", "s_minus");
AssignGeneratorVariables(F);

rels := [
    n_plus^2, n_minus^2, s_plus^2, s_minus^2,
    Comm(n_plus, n_minus),
    Comm(s_plus, s_minus)
];

G := F / rels;
Print("Conformal Parity Group G:\n", G, "\n");
Print("Elements generate the discrete time orientation for the causal structure.\n");
