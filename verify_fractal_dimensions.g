# GAP verification of fractal spacetime dimensions
R := PolynomialRing(Rationals, ["p"]);
p := IndeterminatesOfPolynomialRing(R)[1];

# Verify exact relation Phi^5 - phi^5 = 11 under Phi = p + 1
# by checking if (p+1)^5 - p^5 - 11 = 5 * (p^2 + p - 1) * (p^2 + p + 2)
LHS := (p+1)^5 - p^5 - 11;
RHS := 5 * (p^2 + p - 1) * (p^2 + p + 2);

if LHS = RHS then
    Print("GAP: Fractal dimension relation Phi^5 - phi^5 = 11 verified.\n");
else
    Error("GAP: Fractal dimension relation check failed.\n");
fi;
quit;
