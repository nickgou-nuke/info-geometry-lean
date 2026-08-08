var('x eps k0 k1')
f = exp(x) - 1 - x
fp = diff(f, x)
fpp = diff(fp, x)
assert fp == exp(x) - 1
assert f.subs(x=0) == 0
assert fpp == exp(x)
for val in [-3,-1,0,1,3]:
    assert RDF(f.subs(x=val)) >= 0
K = diagonal_matrix(SR, [k0,k1])
psi_i = vector(SR, [1,0])
psi_f_same = vector(SR, [1,0])
psi_f_orth = vector(SR, [0,1])
num_same = (psi_f_same.row()*K*psi_i.column())[0,0]
den_same = (psi_f_same.row()*psi_i.column())[0,0]
den_orth = (psi_f_orth.row()*psi_i.column())[0,0]
assert den_same == 1
assert den_orth == 0
assert num_same == k0
S = diagonal_matrix(SR, [exp(eps*k0)-1-eps*k0, exp(eps*k1)-1-eps*k1])
assert S.subs({k0:0,k1:0,eps:1}) == zero_matrix(SR,2)
print({'f_zero': f.subs(x=0), 'f_prime': fp, 'sample_nonnegative': True, 'vacuum_zero': True, 'weak_value_same': num_same/den_same, 'orthogonal_denominator': den_orth, 'trace_status':'not_trace_class_in_infinite_GNS'})
