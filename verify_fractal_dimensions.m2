-- Macaulay2 verification of fractal spacetime dimensions
R = QQ;
S = R[p];

-- Verify exact relation Phi^5 - phi^5 = 11 under Phi = p + 1
-- by checking if (p+1)^5 - p^5 - 11 = 5 * (p^2 + p - 1) * (p^2 + p + 2)
LHS = (p+1)^5 - p^5 - 11;
RHS = 5 * (p^2 + p - 1) * (p^2 + p + 2);

assert(LHS == RHS);
print "Macaulay2: Fractal dimension relation Phi^5 - phi^5 = 11 verified."
exit 0
