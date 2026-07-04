-- tools/macaulay2/mobius_generators.m2
R = QQ[a,b,c,d]
M = matrix{{a,b},{c,d}}

-- Projective matrices for Mobius generators
T1 = matrix{{c,d},{0,c}}              -- Translation by d/c
Inv = matrix{{0,1},{1,0}}             -- Inversion
S = matrix{{b*c-a*d, 0}, {0, c^2}}    -- Scaling by (bc-ad)/c^2
T2 = matrix{{c,a},{0,c}}              -- Translation by a/c

-- Multiply them sequentially
P = T2 * S * Inv * T1

-- Generate the ideal mapping to the generic matrix
-- To confirm projectively proportional, check that 2x2 minors of the matrix formed by flattened vectors is zero
vP = flatten entries P
vM = flatten entries M
PropMat = matrix {vP, vM}

-- Verify the syzygies confirm the matrix product is projectively proportional to the original
syzIdeal = minors(2, PropMat)

print("Product Matrix P:");
print(P);
print("Syzygy Ideal of 2x2 minors:");
print(syzIdeal);

-- Check if the ideal is indeed zero
assert(syzIdeal == ideal(0_R))
print("SUCCESS: The matrix product is projectively proportional to the original generic matrix.")
