# tools/gap/mobius_poles.g
F := GF(11);

# Select a non-parabolic invertible matrix [[a,b],[c,d]] where c <> 0
# M = [[2, 3], [4, 5]] over GF(11)
a := 2 * Z(11)^0;
b := 3 * Z(11)^0;
c := 4 * Z(11)^0;
d := 5 * Z(11)^0;

tr := a + d;
det := a * d - b * c;

# We assume det <> 0, tr^2 <> 4*det, c <> 0
# det = 10 - 12 = -2 = 9 <> 0
# tr = 7
# tr^2 = 49 = 5
# 4*det = 36 = 3
# 5 <> 3, so non-parabolic
# c = 4 <> 0

z_inf := -d / c;
Z_inf := a / c;

Print("Matrix: [[", a, ", ", b, "], [", c, ", ", d, "]]\n");
Print("z_infty = ", z_inf, "\n");
Print("Z_infty = ", Z_inf, "\n");
Print("z_infty + Z_infty = ", z_inf + Z_inf, "\n");

x := Indeterminate(F, "x");
poly := c * x^2 + (d - a) * x - b;

# Extract roots over the splitting field (GF(11) or GF(11^2))
L := SplittingField(poly);
roots := RootsOfUPol(L, poly);

gamma1 := roots[1];
gamma2 := roots[2];

Print("gamma_1 = ", gamma1, "\n");
Print("gamma_2 = ", gamma2, "\n");
Print("gamma_1 + gamma_2 = ", gamma1 + gamma2, "\n");

if gamma1 + gamma2 = z_inf + Z_inf then
    Print("Success: Parallelogram relation gamma_1 + gamma_2 = z_infty + Z_infty (mod 11) verified!\n");
else
    Print("Error: Parallelogram relation failed!\n");
fi;
quit;
