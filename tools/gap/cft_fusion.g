alpha := Indeterminate(Rationals, "alpha");
b := Indeterminate(Rationals, "b");

RangeStep2 := function(start_val, end_val)
    local lst, curr;
    lst := [];
    curr := start_val;
    while curr <= end_val do
        Add(lst, curr);
        curr := curr + 2;
    od;
    return lst;
end;

FusionShifts := function(r, s)
    local k, l, shifts;
    shifts := [];
    for k in RangeStep2(1-r, r-1) do
        for l in RangeStep2(1-s, s-1) do
            Add(shifts, alpha + k * b / 2 + l / (2 * b));
        od;
    od;
    return shifts;
end;

shifts_1_2 := FusionShifts(1, 2);
Print("Fusion shifts for V_{1,2} with V_alpha:\n");
Print(shifts_1_2, "\n");

expected_shifts := [ alpha - 1/(2*b), alpha + 1/(2*b) ];
Print("Expected shifts:\n");
Print(expected_shifts, "\n");

if shifts_1_2 = expected_shifts then
    Print("Proof successful: The derived dimensional boundaries map identically to [alpha - 1/(2b), alpha + 1/(2b)]\n");
else
    Print("Proof failed.\n");
fi;

quit;
