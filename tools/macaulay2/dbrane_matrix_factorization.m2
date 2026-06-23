-- tools/macaulay2/dbrane_matrix_factorization.m2
-- Computes the matrix factorization of the quadric q over CC

R = CC[E, px, py, pz]
q = E^2 - px^2 - py^2 - pz^2

-- Define the two matrices of the factorization
D0 = matrix{{E + pz, px - ii*py}, {px + ii*py, E - pz}}
D1 = matrix{{E - pz, -px + ii*py}, {-px - ii*py, E + pz}}

-- Verify D0 * D1 = q * I
I2 = id_(R^2)
relation = D0 * D1 - q * I2

print "Verifying the Matrix Factorization relation (D0 * D1 - q * I):"
print relation
