# GAP verification of Fibonacci partition relations
# 1. Algebraic difference identity
x := Indeterminate(Rationals, "x");
B := 1 / (1 - x);
F := 1 + x;
diff := B - F;
expected := x^2 / (1 - x);

if diff = expected then
    Print("GAP: Partition function supersymmetry difference identity verified.\n");
else
    Error("GAP: Identity check failed.\n");
fi;
quit;
