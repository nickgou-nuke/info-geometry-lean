F := GF(11);
G := PGL(2, 11);
Print("Generated group: ", G, "\n");

# Choose an arbitrary matrix M in GL(2, 11)
M := [[Z(11)^0, 2*Z(11)^0], [3*Z(11)^0, 4*Z(11)^0]];

# Construct the fractional linear transformation function for a matrix
FracLinearTrans := function(mat)
    return function(z)
        local a, b, c, d, num, den;
        a := mat[1][1];
        b := mat[1][2];
        c := mat[2][1];
        d := mat[2][2];
        num := a * z + b;
        den := c * z + d;
        if den = 0 * Z(11) then
            return "infinity";
        else
            return num / den;
        fi;
    end;
end;

f_M := FracLinearTrans(M);

# Construct the function for 3 * M mod 11
# In GF(11), 3 is 3 * Z(11)^0
M3 := 3 * Z(11)^0 * M;

f_M3 := FracLinearTrans(M3);

# Show they are identical for all z in F_11
all_match := true;
for z in Elements(F) do
    val_M := f_M(z);
    val_M3 := f_M3(z);
    Print("z = ", z, ": f_M(z) = ", val_M, ", f_M3(z) = ", val_M3, "\n");
    if val_M <> val_M3 then
        all_match := false;
    fi;
od;

if all_match then
    Print("\nSUCCESS: Evaluated outputs are identical for all z in F_11.\n");
else
    Print("\nFAILURE: Evaluated outputs differ.\n");
fi;

QUIT;
