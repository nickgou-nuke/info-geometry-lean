-- tools/macaulay2/cft_structure.m2

-- Define polynomial field parameters
R = QQ[D_1, D_2, D_3]

-- Define the exponents
E_1 = D_3 - D_1 - D_2
E_2 = D_1 - D_2 - D_3
E_3 = D_2 - D_3 - D_1

-- Define permutations of the dimensions
p12 = map(R, R, {D_2, D_1, D_3})
p13 = map(R, R, {D_3, D_2, D_1})
p23 = map(R, R, {D_1, D_3, D_2})
p123 = map(R, R, {D_2, D_3, D_1})
p132 = map(R, R, {D_3, D_1, D_2})

-- Prove mathematically that exact symmetry constraints evaluate trivially and strictly across permutations
-- Exponent E_1 is invariant under 1 <-> 2
assert(p12(E_1) - E_1 == 0)

-- Exponent E_2 is invariant under 2 <-> 3
assert(p23(E_2) - E_2 == 0)

-- Exponent E_3 is invariant under 1 <-> 3
assert(p13(E_3) - E_3 == 0)

-- Cyclic permutation constraints
assert(p123(E_1) - E_2 == 0)
assert(p123(E_2) - E_3 == 0)
assert(p123(E_3) - E_1 == 0)

-- Anti-cyclic permutation constraints
assert(p132(E_1) - E_3 == 0)
assert(p132(E_3) - E_2 == 0)
assert(p132(E_2) - E_1 == 0)

print("SUCCESS: Exact symmetry constraints evaluate trivially and strictly across permutations.")
