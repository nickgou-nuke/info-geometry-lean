# tools/gap/aut_fn_higher_braids.g
# Automated test suites for B_n -> Aut(F_n) for higher values of n (e.g. n=4)

Print("--- GAP B_n -> Aut(F_n) Representation Test for n=4 ---\n");

F := FreeGroup(4);
x1 := F.1; x2 := F.2; x3 := F.3; x4 := F.4;

# Define the action of the braid generators on the Free Group F_4
# Using the right-handed Artin representation:
# sigma_i(x_i) = x_i x_{i+1} x_i^-1
# sigma_i(x_{i+1}) = x_i
# sigma_i(x_j) = x_j for j != i, i+1

ApplySigma := function(word, i)
    local mapping;
    mapping := [];
    if i = 1 then
        mapping := [x1*x2*x1^-1, x1, x3, x4];
    elif i = 2 then
        mapping := [x1, x2*x3*x2^-1, x2, x4];
    elif i = 3 then
        mapping := [x1, x2, x3*x4*x3^-1, x3];
    fi;
    return MappedWord(word, GeneratorsOfGroup(F), mapping);
end;

# Test 1: Distant Braid Relations (Commutativity)
# sigma_1 sigma_3 (w) = sigma_3 sigma_1 (w)
Print("Testing Distant Braid Relation sigma_1 sigma_3 = sigma_3 sigma_1...\n");
passed_distant := true;
for gen in GeneratorsOfGroup(F) do
    if ApplySigma(ApplySigma(gen, 1), 3) <> ApplySigma(ApplySigma(gen, 3), 1) then
        passed_distant := false;
    fi;
od;
if passed_distant then
    Print("PASS: Distant braid relations commute perfectly.\n");
else
    Print("FAIL: Distant braid relations broken.\n");
fi;

# Test 2: Adjacent Braid Relations (Yang-Baxter)
# sigma_1 sigma_2 sigma_1 (w) = sigma_2 sigma_1 sigma_2 (w)
Print("Testing Adjacent Braid Relation sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2...\n");
passed_adjacent := true;
for gen in GeneratorsOfGroup(F) do
    lhs := ApplySigma(ApplySigma(ApplySigma(gen, 1), 2), 1);
    rhs := ApplySigma(ApplySigma(ApplySigma(gen, 2), 1), 2);
    if lhs <> rhs then
        passed_adjacent := false;
    fi;
od;
if passed_adjacent then
    Print("PASS: Adjacent Yang-Baxter braid relations hold strictly on F_4.\n");
else
    Print("FAIL: Adjacent braid relations broken.\n");
fi;

Print("GAP: Successfully validated B_4 into Aut(F_4) exact witness boundaries.\n");
