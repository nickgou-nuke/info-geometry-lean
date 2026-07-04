C := Indeterminate(Rationals, "C");
z1 := Indeterminate(Rationals, "z1");
z2 := Indeterminate(Rationals, "z2");

WardK2 := function(c, z_1, z_2, d1, d2)
    return c * (z_1 - z_2) * (d1 - d2);
end;

Print("Starting WardK2 invariant checks...\n");

for D1 in [1..5] do
    for D2 in [1..5] do
        val := WardK2(C, z1, z2, D1, D2);
        if val = 0*C then
            Print("D1=", D1, " D2=", D2, " -> WardK2 is zero. Invariant D1=D2 is ", D1=D2, "\n");
            if D1 <> D2 then
                Print("ERROR: Invariant violated!\n");
            fi;
        else
            if D1 = D2 then
                Print("ERROR: WardK2 is non-zero but D1=D2!\n");
            fi;
        fi;
    od;
od;

Print("Finished WardK2 invariant checks.\n");
quit;
