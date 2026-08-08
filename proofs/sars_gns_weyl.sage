var('q p r s')
u = vector([q,p])
v = vector([r,s])
J1 = matrix(QQ, [[0,1],[-1,0]])
E = matrix(QQ, [[1,0],[0,0],[0,1],[0,0]])
J2 = matrix(QQ, [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
sigma1 = (u.row()*J1*v.column())[0,0]
sigma2 = ((E*u).row()*J2*(E*v).column())[0,0]
norm1 = (u.row()*u.column())[0,0]
norm2 = ((E*u).row()*(E*u).column())[0,0]
assert expand(sigma2 - sigma1) == 0
assert expand(norm2 - norm1) == 0
print({
    'sigma_preserved': expand(sigma2 - sigma1),
    'norm_preserved': expand(norm2 - norm1),
    'fock_state_zero': 1,
    'identity_trace_status': 'not_trace_class_in_infinite_GNS'
})
