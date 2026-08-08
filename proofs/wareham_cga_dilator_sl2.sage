I2 = identity_matrix(QQ,2)
e = matrix(QQ, [[1,0],[0,-1]])
ebar = matrix(QQ, [[0,1],[-1,0]])
S = e*ebar
n = e + ebar
nbar = e - ebar
Z2 = zero_matrix(QQ,2)

def comm(A,B): return A*B - B*A
def anticomm(A,B): return A*B + B*A

H = -S
E = QQ(1)/2*n
F = QQ(1)/2*nbar
Casimir = H*H + 2*(E*F + F*E)
assert e*e == I2
assert ebar*ebar == -I2
assert anticomm(e, ebar) == Z2
assert S*S == I2
assert S*n == -n
assert n*S == n
assert S*nbar == nbar
assert nbar*S == -nbar
assert anticomm(S,n) == Z2
assert anticomm(S,nbar) == Z2
assert anticomm(n,nbar) == 4*I2
assert comm(S,n) == -2*n
assert comm(S,nbar) == 2*nbar
assert comm(n,nbar) == -4*S
assert comm(H,E) == 2*E
assert comm(H,F) == -2*F
assert comm(E,F) == H
assert Casimir == 3*I2
assert comm(Casimir,H) == Z2
assert comm(Casimir,E) == Z2
assert comm(Casimir,F) == Z2
edges = ['generated_by','anticommutes_with','closes_to','has_casimir','isomorphic_to']
print({'S_square': 1, 'anticomm_S_n': 0, 'anticomm_n_nbar': 4, 'comm_S_n': '-2n', 'comm_n_nbar': '-4S', 'sl2': True, 'casimir': 3, 'casimir_central': True, 'edges': len(edges)})
