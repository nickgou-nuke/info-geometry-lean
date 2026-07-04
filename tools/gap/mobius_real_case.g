G := SL(2, 11);
elements := AsList(G);

# Compute trace squared for all elements
traces_sq := Set(List(elements, g -> TraceMat(g)^2));

# Convert GF(11) elements to integers
# Note: Int(0*Z(11)) is 0, Int(Z(11)^i) is the integer representation mod 11
traces_sq_int := Set(List(traces_sq, Int));

# The expected set of quadratic residues mod 11
residues := Set([0, 1, 3, 4, 5, 9]);

Print("Trace squared values mod 11: ", traces_sq_int, "\n");
Print("Expected quadratic residues: ", residues, "\n");

if IsSubset(residues, traces_sq_int) then
    Print("Success: All trace squared values are valid quadratic residues in GF(11).\n");
else
    Print("Error: Some trace squared values are not quadratic residues.\n");
fi;

QUIT;
