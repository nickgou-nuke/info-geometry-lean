S = QQ[D1, D2];
W = frac(S)[z1, z2, d1, d2, WeylAlgebra => {z1 => d1, z2 => d2}];

Wm1 = d1 + d2;
W0 = z1*d1 + z2*d2 + D1 + D2;
W1 = z1^2*d1 + z2^2*d2 + 2*D1*z1 + 2*D2*z2;

comm = W1*Wm1 - Wm1*W1;
expected = -2*W0;

if comm == expected then (
    print "Success: W1 W_{-1} - W_{-1} W1 = -2 W0";
    exit 0;
) else (
    print "Failure: comm != -2 W0";
    print toString comm;
    print toString expected;
    exit 1;
)
