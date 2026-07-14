-- tools/macaulay2/cft_blocks.m2
-- Explicitly lock the cross-ratio conformal boundaries mapping into X.

-- Define the coordinate ring with polynomial parameters
R = QQ[z1, z2, z3, z4, X, a, b];

-- Define the cross-ratio conformal boundary mapping polynomial P
P = (z1-z2)*(z3-z4) - X*(z1-z3)*(z2-z4);

-- Translation generator: z_i -> z_i + a
PTrans = sub(P, {z1 => z1 + a, z2 => z2 + a, z3 => z3 + a, z4 => z4 + a});

-- Dilation generator: z_i -> b * z_i
Pdil = sub(P, {z1 => b * z1, z2 => b * z2, z3 => b * z3, z4 => b * z4});

-- Standard ideal reduction to verify translation invariance
-- Under standard ideal reduction, the translated P should evaluate identically to P
diffTrans = PTrans - P;

-- The dilated P should be b^2 * P
diffDil = Pdil - b^2 * P;

print("Verifying translation invariance (difference should be 0):");
print(diffTrans);

print("Verifying dilation invariance (difference should be 0):");
print(diffDil);
