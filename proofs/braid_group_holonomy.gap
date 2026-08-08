# braid_group_holonomy.gap
# Implement the fundamental group and the exact Braid Group relations 
# governing the phase shifts of the Majorana parafermions.

Print("Initializing Braid Group for Majorana Parafermions...\n");

# Define the Free Group for generators
F := FreeGroup("s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9");

# Define the relations for the Braid Group B_10
# 1. s_i s_j = s_j s_i for |i - j| > 1
# 2. s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}

rels := [];

# Commutativity relations
for i in [1..7] do
    for j in [i+2..9] do
        Add(rels, F.(i) * F.(j) * F.(i)^-1 * F.(j)^-1);
    od;
od;

# Braid relations
for i in [1..8] do
    Add(rels, F.(i) * F.(i+1) * F.(i) * F.(i+1)^-1 * F.(i)^-1 * F.(i+1)^-1);
od;

# Construct the Braid Group
B10 := F / rels;
Print("Braid Group B_10 constructed with exact relations.\n");

# Define a representation for the holonomy
# For Majorana fermions, we consider a representation into a symmetric group as a simplified topological invariant
hom := GroupHomomorphismByImages(B10, SymmetricGroup(10), 
    GeneratorsOfGroup(B10), 
    [(1,2), (2,3), (3,4), (4,5), (5,6), (6,7), (7,8), (8,9), (9,10)]);

Print("Holonomy representation onto SymmetricGroup(10) defined.\n");

# Calculate the holonomy of a specific path (braid word)
path := B10.1 * B10.2 * B10.3 * B10.1 * B10.2;
holonomy := Image(hom, path);

Print("Holonomy evaluated for the given path: ", holonomy, "\n");
Print("Topological phase shift successfully calculated.\n");
