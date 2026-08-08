# orbifold_monodromy.gap
# Implement the Braid Group Monodromy representing the canonical twisting
# of the vector bundles over the Riemann sheets.

Print("Braid Group Monodromy for Twisted Vector Bundles\n");

# We consider a generic braid group acting on sheets
n_sheets := 4;
F := FreeGroup(n_sheets - 1);
gens := GeneratorsOfGroup(F);

# Define the Braid group presentation B_n
rels := [];
for i in [1..n_sheets-2] do
    Add(rels, gens[i]*gens[i+1]*gens[i] * (gens[i+1]*gens[i]*gens[i+1])^-1);
od;

for i in [1..n_sheets-3] do
    for j in [i+2..n_sheets-1] do
        Add(rels, gens[i]*gens[j] * (gens[j]*gens[i])^-1);
    od;
od;

B_n := F / rels;
Print("Braid Group B_", n_sheets, " defined with relations:\n");
Display(rels);

# Monodromy representation can be mapped to symmetric group as a toy model for sheets
S_n := SymmetricGroup(n_sheets);
hom := GroupHomomorphismByImages(B_n, S_n, GeneratorsOfGroup(B_n), 
       List([1..n_sheets-1], i -> (i, i+1)));

Print("Monodromy representation to S_", n_sheets, " defined.\n");
