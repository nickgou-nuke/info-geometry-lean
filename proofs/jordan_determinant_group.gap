# jordan_determinant_group.gap

# Create a finite matrix group, e.g., GL(2, 3)
G := GL(2, 3);
   
q := 3;
Z_q_minus_1 := Integers mod (q-1);

# Primitive element of GF(q)
F := GaloisField(q);
z := Z(q);

# Define the log det homomorphism
# Homomorphism from GL(n, q) to additive group of integers modulo q-1
LogDetHomomorphism := function(M)
    local d, e;
    d := Determinant(M);
    if d = 0*Z(q) then
        Error("Matrix not invertible");
    fi;
    # Find discrete log base z
    e := LogFFE(d, z);
    return e * Z_q_minus_1;
end;

# Test the homomorphism property
g1 := Random(G);
g2 := Random(G);

Print("Group element g1:\n", g1, "\n\n");
Print("Group element g2:\n", g2, "\n\n");

Print("LogDet(g1 * g2) = ", LogDetHomomorphism(g1 * g2), "\n");
Print("LogDet(g1) + LogDet(g2) = ", LogDetHomomorphism(g1) + LogDetHomomorphism(g2), "\n");
