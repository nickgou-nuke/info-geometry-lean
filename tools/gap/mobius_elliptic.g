F := GF(11);
S := [ [ 0, -1 ], [ 1, 0 ] ] * Z(11)^0;
Print("Trace-0 elliptic matrix S over GF(11):\n");
Print(S, "\n\n");

a := S[1][1];
b := S[1][2];
c := S[2][1];
d := S[2][2];

z := Indeterminate(F, "z");
eq := c * z^2 + (d - a) * z - b;

Print("Fixed-point boundary equation: ", eq, " = 0\n");

roots := Filtered(AsList(F), v -> Value(eq, v) = 0*Z(11));

Print("Roots over GF(11): ", roots, "\n");
Print("Number of roots: ", Length(roots), "\n\n");

Print("Over GF(11), z^2 + 1 = 0 has exactly 0 roots (because 11 is 3 mod 4, the roots only exist in the GF(11^2) Galois extension),\n");
Print("perfectly mirroring the Real continuous geometric properties of Elliptic transforms where real fixed points do not exist!\n");
QUIT;
