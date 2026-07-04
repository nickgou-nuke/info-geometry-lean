F := GF(11);
one := One(F);
a := 1 * one;
b := 2 * one;
c := 3 * one;
d := 4 * one;

M := [[a, b], [c, d]];

Print("Original matrix M:\n");
Display(M);

T_dc := [[one, d/c], [0*one, one]];
J := [[0*one, one], [one, 0*one]];
H := [[(b*c-a*d)/(c^2), 0*one], [0*one, one]];
T_ac := [[one, a/c], [0*one, one]];

Print("T_{d/c}:\n");
Display(T_dc);
Print("J:\n");
Display(J);
Print("H:\n");
Display(H);
Print("T_{a/c}:\n");
Display(T_ac);

P := T_ac * H * J * T_dc;

Print("Product P:\n");
Display(P);

scalar := P[2][1] / M[2][1];

Print("Scalar = ", scalar, "\n");
Print("Is P = scalar * M ? ", P = scalar * M, "\n");

if P = scalar * M then
    Print("SUCCESS: The product is projectively equivalent to M.\n");
else
    Print("FAILURE: The product is not projectively equivalent to M.\n");
fi;
quit;
