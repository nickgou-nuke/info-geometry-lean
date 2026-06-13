# GAP finite Coxeter quotient witness for D-type braid closures.
#
# This is deliberately a finite group-theoretic smoke test.  It checks that the
# Artin presentation with Coxeter involution relations collapses to the Weyl
# groups W(D4) and W(D5).  It does not prove that a Fibonacci anyon braid image
# is W(D4) or W(D5), and it does not connect spin/SUSY matrices to root
# operators.  Those remain Lean-side adapter obligations.

Print("=== ANYON / WEYL FINITE QUOTIENT VALIDATION ===\n");

RequireTrue := function(name, cond)
    if not cond then
        Error(Concatenation("validation failed: ", name));
    fi;
    Print("[OK] ", name, "\n");
end;

AlternatingWord := function(F, a, b, len)
    local gens, word, k;
    gens := GeneratorsOfGroup(F);
    word := One(F);
    for k in [1..len] do
        if k mod 2 = 1 then
            word := word * gens[a];
        else
            word := word * gens[b];
        fi;
    od;
    return word;
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
    Print("[INFO] ", label, " Coxeter order = ", Size(G), "\n");
    RequireTrue(Concatenation(label, " has expected order"), Size(G) = expectedOrder);
    return G;
end;

ArtinCoxeterQuotient := function(label, coxeterMatrix, expectedOrder)
    local F, gens, rels, i, j, m, lhs, rhs, G;
    F := FreeGroup(Length(coxeterMatrix));
    gens := GeneratorsOfGroup(F);
    rels := [];

    # Finite quotient of the Artin presentation: impose reflection involutions.
    for i in [1..Length(coxeterMatrix)] do
        Add(rels, gens[i]^2);
    od;

    # Alternating Artin relation of length m_ij.
    for i in [1..Length(coxeterMatrix)] do
        for j in [i + 1..Length(coxeterMatrix)] do
            m := coxeterMatrix[i][j];
            lhs := AlternatingWord(F, i, j, m);
            rhs := AlternatingWord(F, j, i, m);
            Add(rels, lhs * rhs^-1);
        od;
    od;

    G := F / rels;
    Print("[INFO] ", label, " Artin/Coxeter quotient order = ", Size(G), "\n");
    RequireTrue(Concatenation(label, " has expected Weyl quotient order"),
        Size(G) = expectedOrder);
    return G;
end;

NaturalGeneratorMapIsBijective := function(source, target)
    local hom;
    hom := GroupHomomorphismByImages(
        source,
        target,
        GeneratorsOfGroup(source),
        GeneratorsOfGroup(target));
    if hom = fail then
        return false;
    fi;
    return IsBijective(hom);
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

BD4 := ArtinCoxeterQuotient("D4", D4Matrix, 192);
BD5 := ArtinCoxeterQuotient("D5", D5Matrix, 1920);

RequireTrue("natural D4 Artin/Coxeter generator map is bijective",
    NaturalGeneratorMapIsBijective(BD4, WD4));
RequireTrue("natural D5 Artin/Coxeter generator map is bijective",
    NaturalGeneratorMapIsBijective(BD5, WD5));

PermD4 := Image(IsomorphismPermGroup(WD4));
PermD5 := Image(IsomorphismPermGroup(WD5));
IrrD4 := Irr(CharacterTable(PermD4));
IrrD5 := Irr(CharacterTable(PermD5));

Print("[INFO] W(D4) irreducible character count = ", Length(IrrD4), "\n");
Print("[INFO] W(D5) irreducible character count = ", Length(IrrD5), "\n");
RequireTrue("W(D4) has a two-dimensional irreducible character",
    ForAny(IrrD4, chi -> chi[1] = 2));

Print("[SUCCESS] D-type finite braid quotients validated against W(D4) and W(D5).\n");
Print("[NOTE] GAP witness only: no categorical hexagon, anyon-image, or Lean-kernel closure claimed.\n");
QUIT;
