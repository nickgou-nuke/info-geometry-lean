import sympy as sp

q,p,r,s = sp.symbols('q p r s', real=True)
u = sp.Matrix([q,p])
v = sp.Matrix([r,s])
J1 = sp.Matrix([[0,1],[-1,0]])
E = sp.Matrix([[1,0],[0,0],[0,1],[0,0]])
J2 = sp.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])

sigma1 = (u.T * J1 * v)[0]
sigma2 = ((E*u).T * J2 * (E*v))[0]
norm1 = (u.T*u)[0]
norm2 = ((E*u).T*(E*u))[0]
phase1 = sp.exp(-sp.I*sigma1/2)
phase2 = sp.exp(-sp.I*sigma2/2)
fock1 = sp.exp(-norm1/4)
fock2 = sp.exp(-norm2/4)

assert sp.simplify(sigma2 - sigma1) == 0
assert sp.simplify(norm2 - norm1) == 0
assert sp.simplify(phase2 - phase1) == 0
assert sp.simplify(fock2 - fock1) == 0
assert sp.exp(0) == 1

print({
    'sigma_preserved': sp.simplify(sigma2 - sigma1),
    'norm_preserved': sp.simplify(norm2 - norm1),
    'weyl_phase_preserved': sp.simplify(phase2 - phase1) == 0,
    'fock_state_preserved': sp.simplify(fock2 - fock1) == 0,
    'fock_state_zero': 1,
    'identity_trace_status': 'not_trace_class_in_infinite_GNS'
})
