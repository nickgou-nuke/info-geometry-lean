# Exact-rational Sage certificate for finite holographic Cuntz shard algebra.

R.<x1,x2> = PolynomialRing(QQ)
S = matrix(QQ, [[0,1],[0,0]])
Psource = matrix(QQ, [[0,0],[0,1]])
Paperture = matrix(QQ, [[1,0],[0,0]])
x = vector(R, [x1, x2])
assert S.transpose() * S == Psource
assert S * S.transpose() == Paperture
assert (S.transpose() * S).change_ring(R) * x == Psource.change_ring(R) * x
assert Psource * Psource == Psource
assert Paperture * Paperture == Paperture
assert S * S.transpose() * S == S
T = matrix(QQ, [[0,0],[1,0]])
assert S.transpose()*S + T.transpose()*T == identity_matrix(QQ, 2)
print("holographic Cuntz shard Sage certificate: ok")
