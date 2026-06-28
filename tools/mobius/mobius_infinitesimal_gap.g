# sl(2,C) Infinitesimal/Exponential Packet in GAP
# Pure-math verification of trace-zero 2x2 matrices and discriminant

# Define matrix constructor for sl2 triple
sl2Matrix := function(a, b, c)
    return [ [ a, b ], [ c, -a ] ];
end;;

# Compute determinant
det2 := function(M)
    return M[1][1] * M[2][2] - M[1][2] * M[2][1];
end;;

# Compute discriminant of the vector field
ComputeDiscriminant := function(M)
    local a, b, c;
    a := M[1][1];
    b := M[1][2];
    c := M[2][1];
    return 4 * a^2 + 4 * b * c;
end;;

# Packet samples
packets := rec(
    parabolic := [ [ 1, 1 ], [ -1, -1 ] ],
    hyperbolic := [ [ 1, 0 ], [ -1, -1 ] ],
    elliptic := [ [ 0, 1 ], [ -1, 0 ] ],
    loxodromic := [ [ 1, 1 ], [ E(4), -1 ] ]  # E(4) = i in GAP
);

# Verify each packet
Print("=== GAP: sl(2,C) Infinitesimal/Exponential Packet ===\n\n");

names := [ "parabolic", "hyperbolic", "elliptic", "loxodromic" ];;

for name in names do
    M := packets.(name);
    detM := det2(M);
    delta := ComputeDiscriminant(M);
    
    Print("[", name, "]\n");
    Print("  Matrix = ", M, "\n");
    Print("  Determinant = ", detM, "\n");
    Print("  Discriminant = ", delta, "\n");
    
    # Classification check
    if name = "parabolic" then
        if delta <> 0 then
            Error("Parabolic discriminant should be 0");
        fi;
    elif name = "hyperbolic" then
        if delta <> 4 then
            Error("Hyperbolic discriminant should be 4");
        fi;
    elif name = "elliptic" then
        if delta <> -4 then
            Error("Elliptic discriminant should be -4");
        fi;
    elif name = "loxodromic" then
        # Complex discriminant, just verify it's computed
    fi;
    
    Print("  OK\n\n");
od;

Print("MOBIUS_INFINITESIMAL_GAP_OK\n");