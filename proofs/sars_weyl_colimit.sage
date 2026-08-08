var('q1 p1 r1 s1')
J1 = matrix(QQ, [[0,1],[-1,0]])
J2 = matrix(QQ, [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
E = matrix(QQ, [[1,0],[0,0],[0,1],[0,0]])
u = vector([q1,p1])
v = vector([r1,s1])
sigma1 = (u.row() * J1 * v.column())[0,0]
sigma2 = ((E*u).row() * J2 * (E*v).column())[0,0]
assert expand(sigma2 - sigma1) == 0
assert 32^0 == 1
assert 32^1 == 32
assert 32^2 == 1024
assert 2^10 == 32^2
print({
    'sigma1': sigma1,
    'sigma2_minus_sigma1': expand(sigma2 - sigma1),
    'block_dim_0': 32^0,
    'block_dim_1': 32^1,
    'block_dim_2': 32^2,
    'cl55_dim': 2^10,
    'cl55_equals_block2': 2^10 == 32^2
})
