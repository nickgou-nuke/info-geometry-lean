# Hyperplane reflection in GF(11)^3
F := GF(11);
one := One(F);
a := [1, 2, 3] * one;
r := 5 * one;
x := [4, 5, 6] * one;

R := function(x, a, r)
    local dot_aa, dot_xa, factor, two;
    two := 2 * one;
    dot_aa := a * a;
    dot_xa := x * a;
    factor := two * (dot_xa - r) * dot_aa^-1;
    return x - factor * a;
end;

Print("Original x: ", x, "\n");
R1 := R(x, a, r);
Print("After one reflection: ", R1, "\n");
R2 := R(R1, a, r);
Print("After two reflections: ", R2, "\n");

if R2 = x then
    Print("Success: Hyperplane reflection is an involution!\n");
else
    Print("Failure: Hyperplane reflection is NOT an involution.\n");
fi;

QUIT;
