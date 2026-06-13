# ==============================================================================
# GAP automated finite quotient check for D-type anyon braid interfaces.
#
# Scope: this is a finite group smoke test only.  It validates D4/D5 Coxeter
# quotient presentations and their Artin/Coxeter braid quotients.  It is not a
# Lean kernel proof and it does not assert a laboratory-model realization.
# ==============================================================================

Print("=== ANYON BRAID FINITE QUOTIENT / D-TYPE WEYL VALIDATION ===\n");

RequireTrue := function(name, cond)
    if not cond then
        Error(Concatenation("validation failed: ", name));
    fi;
    Print("[OK] ", name, "\n");
end;

CoxeterQuotient := function(label, coxeterMatrix, expectedOrder)
    local F, gens, rels, i, j, G;
    F := FreeGroup(Length(coxeterMatrix));
    gens := GeneratorsOfGroup(F);
    rels := [];
    for i in [1..Length(coxeterMatrix)] do
        Add(rels, gens[i]^2);
    od;
    for i in [1..Length(coxeterMatrix)] do
        for j in [i + 1..Length(coxeterMatrix)] do
            Add(rels, (gens[i] * gens[j])^coxeterMatrix[i][j]);
        od;
    od;
    G := F / rels;
    Print("[INFO] ", label, " order = ", Size(G), "\n");
    RequireTrue(Concatenation(label, " has expected order"), Size(G) = expectedOrder);
    return G;
end;

D4Matrix := [
    [1, 3, 2, 2],
    [3, 1, 3, 3],
    [2, 3, 1, 2],
    [2, 3, 2, 1]
];

D5Matrix := [
    [1, 3, 2, 2, 2],
    [3, 1, 3, 2, 2],
    [2, 3, 1, 3, 3],
    [2, 2, 3, 1, 2],
    [2, 2, 3, 2, 1]
];

WD4 := CoxeterQuotient("W(D4)", D4Matrix, 192);
WD5 := CoxeterQuotient("W(D5)", D5Matrix, 1920);

ArtinCoxeterQuotient := function(label, coxeterMatrix, expectedOrder)
    local F, gens, rels, i, j, m, lhs, rhs, k, G;
    F := FreeGroup(Length(coxeterMatrix));
    gens := GeneratorsOfGroup(F);
    rels := [];

    # Finite quotient of the Artin braid-type presentation: impose sigma_i^2 = 1.
    for i in [1..Length(coxeterMatrix)] do
        Add(rels, gens[i]^2);
    od;

    # Alternating Artin braid relation of length m_ij.
    for i in [1..Length(coxeterMatrix)] do
        for j in [i + 1..Length(coxeterMatrix)] do
            m := coxeterMatrix[i][j];
            lhs := One(F);
            rhs := One(F);
            for k in [1..m] do
                if k mod 2 = 1 then
                    lhs := lhs * gens[i];
                    rhs := rhs * gens[j];
                else
                    lhs := lhs * gens[j];
                    rhs := rhs * gens[i];
                fi;
            od;
            Add(rels, lhs * rhs^-1);
        od;
    od;

    G := F / rels;
    Print("[INFO] ", label, " finite quotient order = ", Size(G), "\n");
    RequireTrue(Concatenation(label, " has expected Weyl quotient order"),
        Size(G) = expectedOrder);
    return G;
end;

BD4 := ArtinCoxeterQuotient("D4 Artin/Coxeter braid quotient", D4Matrix, 192);
BD5 := ArtinCoxeterQuotient("D5 Artin/Coxeter braid quotient", D5Matrix, 1920);

RequireTrue("D4 braid quotient is isomorphic to W(D4)", IsomorphismGroups(BD4, WD4) <> fail);
RequireTrue("D5 braid quotient is isomorphic to W(D5)", IsomorphismGroups(BD5, WD5) <> fail);

Print("[SUCCESS] Finite D-type braid quotients validated against W(D4) and W(D5).\n");
Print("[NOTE] This is a GAP-side finite quotient smoke test, not a Lean kernel proof.\n");
QUIT;
