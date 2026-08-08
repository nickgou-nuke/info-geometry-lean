charges = [2,2,2,-3,-3]
roots_A4 = [(i,j) for i in range(5) for j in range(5) if i != j]
sm_roots = [(i,j) for (i,j) in roots_A4 if charges[i] == charges[j]]
broken_roots = [(i,j) for (i,j) in roots_A4 if charges[i] != charges[j]]
assert len(roots_A4) == 20
assert len(sm_roots) == 8
assert len(broken_roots) == 12
assert 4 + len(roots_A4) == 24
assert 4 + len(sm_roots) == 12
assert len(broken_roots) == 12
assert 5*5 == 25
assert 5*5 != 4 + len(roots_A4)
assert 5*5 - (4 + len(roots_A4)) == 1
assert sum(binomial(5,k) for k in range(6)) == 32
assert 10*(10-1)//2 == 45
assert 2^10 == 32*32
Gamma = diagonal_matrix(QQ, [1]*16 + [-1]*16)
assert Gamma*Gamma == identity_matrix(QQ,32)
assert Gamma.trace() == 0
assert (Gamma*identity_matrix(QQ,32)).trace() == 0
assert identity_matrix(QQ,32).trace() == 32
R = RootSystem(['A',4]).root_lattice()
W = WeylGroup(['A',4], prefix='s')
assert W.cardinality() == factorial(5)
print({
    'A4_roots': len(roots_A4),
    'SM_roots': len(sm_roots),
    'broken_roots': len(broken_roots),
    'su5_adjoint_dim': 4 + len(roots_A4),
    'sm_adjoint_dim': 4 + len(sm_roots),
    'fundamental_scalar_dim': 25,
    'not_adjoint': 25 != 24,
    'dimension_gap': 1,
    'exterior_c5_dim': sum(binomial(5,k) for k in range(6)),
    'so10_adjoint_dim': 45,
    'cl55_dim': 2^10,
    'trace_gamma': Gamma.trace(),
    'supertrace_identity': (Gamma*identity_matrix(QQ,32)).trace(),
    'weyl_A4_order': W.cardinality()
})
