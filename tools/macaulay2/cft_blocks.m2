-- tools/macaulay2/cft_blocks.m2
R = QQ[z_1, z_2, z_3, z_4, X]

P = (z_1 - z_2)*(z_3 - z_4) - X*(z_1 - z_3)*(z_2 - z_4)

S = QQ[z_1, z_2, z_3, z_4, X, a, l]

phiT = map(S, R, {z_1 + a, z_2 + a, z_3 + a, z_4 + a, X})
PT = phiT(P)
diffT = PT - sub(P, S)

phiD = map(S, R, {l*z_1, l*z_2, l*z_3, l*z_4, X})
PD = phiD(P)
diffD = PD - l^2 * sub(P, S)

print "Cross-ratio polynomial P:"
print P

print "Translation invariance difference (should be 0):"
print diffT

print "Dilation invariance difference (should be 0):"
print diffD

if diffT == 0 and diffD == 0 then (
    print "Conformal invariants check passed: Identical zero evaluations natively under standard ideal reduction.";
    exit 0;
) else (
    print "Error: Conformal invariants check failed.";
    exit 1;
)
