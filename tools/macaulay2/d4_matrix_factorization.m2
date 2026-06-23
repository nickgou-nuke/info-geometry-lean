-- tools/macaulay2/d4_matrix_factorization.m2
-- Computes the matrix factorizations of the D4 superpotential

-- Define the polynomial ring of the D4 singularity over CC
-- We use w where w^2 = z to avoid fractional exponents
R = CC[x, y, w]
W = x^2 + y^2 * w^2 + w^6

-- D0 = matrix{{x + ii*y*w, w^2}, {-w^4, x - ii*y*w}}
-- D1 = matrix{{x - ii*y*w, -w^2}, {w^4, x + ii*y*w}}
D0 = matrix{{x + ii*y*w, w^2}, {-w^4, x - ii*y*w}}
D1 = matrix{{x - ii*y*w, -w^2}, {w^4, x + ii*y*w}}

-- We check D0 * D1 - W * I on the algebraic coordinate ring.
I2 = id_(R^2)
relation = D0 * D1 - W * I2

print "Evaluating the D4 Singular Matrix Factorization (D0 * D1 - W * I):"
print relation
