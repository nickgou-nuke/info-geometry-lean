import sympy as sp

x, eps, k0, k1 = sp.symbols('x eps k0 k1', real=True)
f = sp.exp(x) - 1 - x
fp = sp.diff(f, x)
fpp = sp.diff(fp, x)
assert fp == sp.exp(x) - 1
assert f.subs(x, 0) == 0
assert fpp == sp.exp(x)

vals = [-3, -1, 0, 1, 3]
for val in vals:
    assert float(f.subs(x, val)) >= 0.0

psi_i = sp.Matrix([1, 0])
psi_f_same = sp.Matrix([1, 0])
psi_f_orth = sp.Matrix([0, 1])
K = sp.diag(k0, k1)
num_same = (psi_f_same.T * K * psi_i)[0]
den_same = (psi_f_same.T * psi_i)[0]
den_orth = (psi_f_orth.T * psi_i)[0]
assert den_same == 1
assert den_orth == 0
assert num_same == k0

S = sp.diag(sp.exp(eps*k0)-1-eps*k0, sp.exp(eps*k1)-1-eps*k1)
assert S.subs({k0:0,k1:0,eps:1}) == sp.zeros(2)

print({
    'f': str(f),
    'f_prime': str(fp),
    'f_zero': f.subs(x,0),
    'sample_nonnegative': True,
    'vacuum_zero': True,
    'weak_denominator_nonzero': den_same,
    'orthogonal_denominator': den_orth,
    'weak_value_same': str(num_same/den_same),
    'orthogonal_weak_value_defined': False,
    'trace_status':'not_trace_class_in_infinite_GNS',
})
