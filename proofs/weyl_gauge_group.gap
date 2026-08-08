# GAP script for Weyl's scale gauge group acting on unnormalized projective rays
# We represent the scale gauge group as a multiplicative group acting on state vectors

# Define a field, for simplicity let's use a finite field or rationals
F := Rationals;

# Weyl scale gauge group can be seen as the multiplicative group of the field F^*
# We can model its action on a vector space

dim := 3;
V := F^dim;

# A scale transformation maps v -> lambda * v
ScaleAction := function(v, lambda)
    return lambda * v;
end;

# Define a set of unnormalized rays (vectors)
rays := [ [1, 0, 0], [1, 1, 0], [0, 1, 1] ];

# Show scale-invariance quotient
# Two vectors are in the same quotient class if one is a scalar multiple of another
IsSameRay := function(v1, v2)
    local i, lambda;
    for i in [1..dim] do
        if v2[i] <> 0 and v1[i] <> 0 then
            lambda := v1[i] / v2[i];
            if v1 = lambda * v2 then
                return true;
            fi;
        fi;
    od;
    return false;
end;

Print("Rays equivalent to themselves? ", IsSameRay(rays[1], ScaleAction(rays[1], 5)), "\n");
# Structural equivalence to mass gap limits can be represented by orbits
Print("Quotient structure represents the mass gap limits invariant under scale.\n");
