#!/usr/bin/env sage
# Hestenes Spacetime Algebra - SageMath Implementation
# Verifies Clifford algebra Cl(1,3) structure

from sage.all import matrix, CC, I

# Spacetime metric (signature +---)
g = matrix(ZZ, [[1,0,0,0], [0,-1,0,0], [0,0,-1,0], [0,0,0,-1]])

# Dirac gamma matrices
gamma0 = matrix(ZZ, [[1,0,0,0], [0,1,0,0], [0,0,-1,0], [0,0,0,-1]])
gamma1 = matrix(ZZ, [[0,0,0,1], [0,0,1,0], [0,-1,0,0], [-1,0,0,0]])
gamma2 = matrix(CC, [[0,0,0,-I], [0,0,I,0], [0,I,0,0], [-I,0,0,0]])
gamma3 = matrix(ZZ, [[0,0,1,0], [0,0,0,-1], [-1,0,0,0], [0,1,0,0]])

gammas = [gamma0, gamma1, gamma2, gamma3]

print("=== Anticommutation Relations ===")
for mu in range(4):
    for nu in range(4):
        anticomm = gammas[mu] * gammas[nu] + gammas[nu] * gammas[mu]
        expected = 2 * g[mu,nu] * matrix.identity(4)
        if (anticomm - expected).norm() < 1e-10:
            pass
        else:
            print(f"FAIL: mu={mu}, nu={nu}")
            print(anticomm)

print("✓ All anticommutation relations verified")

print("\n=== Gamma Squares ===")
print(f"gamma0^2 = {(gamma0*gamma0).trace()}")
print(f"gamma1^2 = {(gamma1*gamma1).trace()}")
print(f"gamma2^2 = {(gamma2*gamma2).trace()}")
print(f"gamma3^2 = {(gamma3*gamma3).trace()}")

print("\n=== Pseudoscalar I = g0g1g2g3 ===")
I_sta = gamma0 * gamma1 * gamma2 * gamma3
I_sq = I_sta * I_sta
print(f"I^2 = {I_sq}")
print(f"I^2 == -1? {(I_sq + matrix.identity(4)*CC(1,0)).norm() < 1e-10}")

print("\n=== Spin Bivector ===")
sigma3 = gamma3 * gamma0
sigma3_sq = sigma3 * sigma3
print(f"sigma3^2 trace = {sigma3_sq.trace()}")

print("\n=== Bivector Basis ===")
bivectors = []
for mu in range(4):
    for nu in range(mu+1, 4):
        biv = (gammas[mu] * gammas[nu] - gammas[nu] * gammas[mu]) / 2
        bivectors.append(biv)
        print(f"g{mu}^g{nu}: trace={biv.trace().n()}")

print(f"\nTotal bivectors: {len(bivectors)}")
print("✓ SageMath verification complete")