-- Macaulay2 script for Pin(5,5) Clifford algebra structure

-- We define a ring with 10 generators for the Gamma matrices
-- Since they are non-commutative, Macaulay2's standard commutative rings won't work out of the box for Clifford algebra without the `NCPolyRing` or similar packages, but we can compute the commutative quotient or use the exterior algebra structure.
-- A standard way to represent the Clifford Algebra in M2 is via the Clifford package if installed, or by taking the tensor algebra quotient.
-- Let's define the commutative center or the structure of the involutions.

R = QQ[j]
-- Ideal for the involution J^2 = 1
I_inv = ideal(j^2 - 1)

-- Projectors
P_plus = (1 + j)/2
P_minus = (1 - j)/2

print "Testing Idempotency in Macaulay2 modulo ideal (j^2 - 1):"
print( P_plus^2 - P_plus % I_inv )
print( P_minus^2 - P_minus % I_inv )
print( P_plus * P_minus % I_inv )

exit
