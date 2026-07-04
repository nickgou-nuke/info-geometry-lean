# tools/gap/mobius_hyperbolic.g
Print("Starting GAP Hyperbolic Mobius Script\n");

F := GF(11);

# Matrix M = [[4, 0], [1, 3]] over GF(11)
a := 4 * Z(11)^0;
b := 0 * Z(11)^0;
c := 1 * Z(11)^0;
d := 3 * Z(11)^0;
M := [[a, b], [c, d]];

detM := a*d - b*c;
Print("Determinant: ", Int(detM), "\n");
if Int(detM) <> 1 then
    Error("Determinant is not 1");
fi;

trM := a + d;
tr2 := trM^2;
Print("Trace squared: ", Int(tr2), "\n");
if Int(tr2) <> 5 then
    Error("Trace squared is not 5");
fi;

# Compute fixed points: c*z^2 + (d-a)*z - b = 0
roots := [];
for z_int in [0..10] do
    z := z_int * Z(11)^0;
    val := c * z^2 + (d - a) * z - b;
    if val = 0 * Z(11)^0 then
        Add(roots, z_int);
    fi;
od;

Print("Fixed points in GF(11): ", roots, "\n");
if Length(roots) = 2 then
    Print("Exactly 2 discrete roots exist natively inside GF(11). Hyperbolic mirrored!\n");
else
    Error("Did not find exactly 2 discrete roots");
fi;

QUIT;
