# parity_permutation.gap
# Formulate Orientability using the parity of permutation groups mapping the vertices of the Birkhoff polytope.

G := SymmetricGroup(3);
vertices := Elements(G);

Print("Vertices of Birkhoff polytope (B_3):\n");
for v in vertices do
    parity := SignPerm(v);
    if parity == 1 then
        Print(v, " is an Even permutation (Preserves Orientation)\n");
    else
        Print(v, " is an Odd permutation (Reverses Orientation)\n");
    fi;
od;
