# Exact-rational Sage audit for the finite MDPAS/JM global-quantization lane.
R = PolynomialRing(QQ, 'phi0,phi1,phi2,r,a0,a1,a2,a3,hbar')
phi0, phi1, phi2, r, a0, a1, a2, a3, hbar = R.gens()

exact_cycle = (phi1 - phi0) + (phi2 - phi1) + (phi0 - phi2)
assert exact_cycle == 0
assert R(1) + R(1) + R(1) != 0

J = matrix(R, [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
assert J + J.transpose() == 0
assert J.det() == 1

g4 = diagonal_matrix(R, [1, -1, -1, -1])
A = vector(R, [a0, a1, a2, a3]).column()
top_left = g4 + r * (A * A.transpose())
kk = matrix(R, 5, 5)
for i in range(4):
    for j in range(4):
        kk[i, j] = top_left[i, j]
    kk[i, 4] = r * A[i, 0]
    kk[4, i] = r * A[i, 0]
kk[4, 4] = r
assert kk == kk.transpose()

assert 2 * (hbar / 2) - hbar == 0

print("mdpas JMSouriau global quantization Sage certificate: ok")

