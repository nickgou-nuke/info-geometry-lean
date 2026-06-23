# Exact-rational Sage certificate for Chao retrocirculants.

R.<m0,m1,m2,m3,m4,m5,m6,m7,x> = PolynomialRing(QQ)
mu = [m0,m1,m2,m3,m4,m5,m6,m7]
n = 8
sigma = {k: (5*k) % n for k in range(n)}
assert all(sigma[sigma[k]] == k for k in range(n))
fixed = [k for k in range(n) if sigma[k] == k]
assert fixed == [0,2,4,6]
cycles = [(1,5),(3,7)]
P = matrix(R, n, n, lambda r,c: 1 if sigma[c] == r else 0)
D = diagonal_matrix(R, mu)
A = P*D
char = (x * identity_matrix(R, n) - A).det()
expected = prod(x - mu[k] for k in fixed) * prod(x^2 - mu[i]*mu[j] for i,j in cycles)
assert char == expected
print("chao retrocirculant Sage certificate: ok")
