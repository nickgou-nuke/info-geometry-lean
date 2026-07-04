R = QQ[a,b,c,d,z,L];
N = a*z + b;
D = c*z + d;

NL = (L*a)*z + (L*b);
DL = (L*c)*z + (L*d);

scaleDiff = NL * D - N * DL;

if scaleDiff == 0 then (
    print "Syzygy evaluates perfectly to zero, confirming scale invariance.";
) else (
    print "Syzygy is not zero!";
    exit 1;
)
