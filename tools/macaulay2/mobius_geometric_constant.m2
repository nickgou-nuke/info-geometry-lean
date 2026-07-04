-- tools/macaulay2/mobius_geometric_constant.m2

-- Define the polynomial ring with variables L (lambda), invL (1/lambda), sigma, and k
R = QQ[L, invL, sigma, k, MonomialOrder=>Lex]

-- Define the ideal representing the algebraic relationships:
-- 1. invL is the inverse of L: L * invL = 1
-- 2. sigma is defined as (L + invL)^2
-- 3. k is defined as L^2
I = ideal(L*invL - 1, sigma - (L + invL)^2, k - L^2)

-- Factor the ideal over variables sigma and k by eliminating L and invL
-- This computes the syzygies / algebraic relations between sigma and k
J = eliminate({L, invL}, I)

print "--- Elimination Ideal (Relations between sigma and k) ---"
print toString J

-- Define the expected relation to prove
expectedRel = sigma*k - (k+1)^2

print "--- Proving sigma*k - (k+1)^2 = 0 ---"
-- Check if the expected relation belongs to the ideal J (meaning it evaluates to 0)
assert (expectedRel % J == 0)
assert (expectedRel % I == 0)

print "Proof successful: sigma*k - (k+1)^2 = 0 is derived from the ideal."

exit 0
