# tools/gap/minimal_models.g
# Formalization of 2D CFT Minimal Models Kac Table

MinimalModel := function(p, q)
    local c, r, s, h_rs, unique_reps, rep, found;

    if Gcd(p, q) <> 1 then
        Error("p and q must be coprime");
    fi;

    # Central charge
    c := 1 - 6 * (p - q)^2 / (p * q);

    unique_reps := [];

    for r in [1 .. p - 1] do
        for s in [1 .. q - 1] do
            # Conformal weight
            h_rs := ((r * q - s * p)^2 - (p - q)^2) / (4 * p * q);

            # Check if identified pair is already in unique_reps
            # We identify (r, s) with (p-r, q-s)
            found := false;
            for rep in unique_reps do
                if (rep.r = p - r and rep.s = q - s) then
                    found := true;
                    break;
                fi;
            od;

            if not found then
                Add(unique_reps, rec(
                    r := r,
                    s := s,
                    h := h_rs
                ));
            fi;
        od;
    od;

    # Verify the number of unique representations
    if Length(unique_reps) <> (p - 1) * (q - 1) / 2 then
        Error("Incorrect number of unique representations");
    fi;

    return rec(
        p := p,
        q := q,
        c := c,
        num_reps := Length(unique_reps),
        reps := unique_reps
    );
end;

# Test with Ising model (p=3, q=4)
ising := MinimalModel(3, 4);
Print("Ising Model (3,4):\n");
Print("Central Charge c = ", ising.c, "\n");
Print("Number of unique representations = ", ising.num_reps, "\n");
for rep in ising.reps do
    Print("  (r=", rep.r, ", s=", rep.s, ") -> h = ", rep.h, "\n");
od;

# Test with Yang-Lee edge singularity (p=2, q=5)
yang_lee := MinimalModel(2, 5);
Print("\nYang-Lee Model (2,5):\n");
Print("Central Charge c = ", yang_lee.c, "\n");
Print("Number of unique representations = ", yang_lee.num_reps, "\n");
for rep in yang_lee.reps do
    Print("  (r=", rep.r, ", s=", rep.s, ") -> h = ", rep.h, "\n");
od;

# Test with Tricritical Ising model (p=4, q=5)
tricritical := MinimalModel(4, 5);
Print("\nTricritical Ising Model (4,5):\n");
Print("Central Charge c = ", tricritical.c, "\n");
Print("Number of unique representations = ", tricritical.num_reps, "\n");
for rep in tricritical.reps do
    Print("  (r=", rep.r, ", s=", rep.s, ") -> h = ", rep.h, "\n");
od;
