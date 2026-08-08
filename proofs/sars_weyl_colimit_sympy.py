import sympy as sp

q1,p1,r1,s1 = sp.symbols('q1 p1 r1 s1')
u1 = sp.Matrix([q1, p1])
v1 = sp.Matrix([r1, s1])
J1 = sp.Matrix([[0, 1], [-1, 0]])
J2 = sp.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
E = sp.Matrix([[1,0],[0,0],[0,1],[0,0]])

sigma1 = (u1.T * J1 * v1)[0]
sigma2 = ((E*u1).T * J2 * (E*v1))[0]

assert sp.simplify(sigma2 - sigma1) == 0
assert 32**0 == 1
assert 32**1 == 32
assert 32**2 == 1024
assert 2**10 == 32**2

phase_sigma = sp.exp(-sp.I * sigma1 / 2)
phase_embedded = sp.exp(-sp.I * sigma2 / 2)
assert sp.simplify(phase_embedded - phase_sigma) == 0

print({
    'sigma1': sigma1,
    'sigma2_minus_sigma1': sp.simplify(sigma2 - sigma1),
    'weyl_phase_preserved': sp.simplify(phase_embedded - phase_sigma) == 0,
    'block_dim_0': 32**0,
    'block_dim_1': 32,
    'block_dim_2': 32**2,
    'cl55_dim': 2**10,
    'cl55_equals_block2': 2**10 == 32**2,
})
