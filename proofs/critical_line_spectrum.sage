# SageMath script
# We construct a matrix D such that D + D^dagger = I
# Let D = 1/2 * I + i * H, where H is a Hermitian matrix.
# Then D^dagger = 1/2 * I - i * H
# D + D^dagger = I
# The eigenvalues of D are lambda = 1/2 + i * h, where h are eigenvalues of H (which are real).
# Thus Re(lambda) = 1/2.

import sage.all
from sage.all import *

# Construct a 2x2 Hermitian matrix H
H = matrix(CDF, [[1, 2+I], [2-I, -1]])
I2 = identity_matrix(CDF, 2)
D = 0.5 * I2 + I * H

print("Matrix D:")
print(D)

D_dagger = D.conjugate_transpose()
print("\nD + D^dagger:")
print(D + D_dagger)

evals = D.eigenvalues()
print("\nEigenvalues of D:")
for ev in evals:
    print(ev)
    print("Real part:", ev.real())
    assert abs(ev.real() - 0.5) < 1e-10
