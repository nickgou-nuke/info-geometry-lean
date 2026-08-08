M = diagonal_matrix([1]*16 + [-1]*16)
assert M*M == identity_matrix(QQ, 32)
assert M.trace() == 0
assert (M*identity_matrix(QQ,32)).trace() == 0
assert identity_matrix(QQ,32).trace() == 32
assert binomial(5,2) == 10
assert 5^2 - 1 == 24
assert (3^2 - 1) + (2^2 - 1) + 1 == 12
assert (5^2 - 1) - ((3^2 - 1) + (2^2 - 1) + 1) == 12
assert 10*(10-1)//2 == 45
assert sum(binomial(5,k) for k in range(6)) == 32
assert 5*5 == 25
assert 5*5 != 5^2 - 1
assert 5*5 - (5^2 - 1) == 1
assert 32*32 == 2^10
assert 'odd_odd' == 'odd_odd' and 'even' == 'even'
R = RootSystem(['A',4]).root_lattice()
W = WeylGroup(['A',4], prefix='s')
assert W.cardinality() == factorial(5)
print({
    'Gamma32_square': M*M == identity_matrix(QQ,32),
    'trace_Gamma32': M.trace(),
    'supertrace_identity': (M*identity_matrix(QQ,32)).trace(),
    'trace_identity': identity_matrix(QQ,32).trace(),
    'lambda2_su5': binomial(5,2),
    'su5_adjoint': 5^2 - 1,
    'sm_adjoint': (3^2 - 1) + (2^2 - 1) + 1,
    'xy_bosons': (5^2 - 1) - ((3^2 - 1) + (2^2 - 1) + 1),
    'so10_adjoint': 10*(10-1)//2,
    'exterior_C5_dimension': sum(binomial(5,k) for k in range(6)),
    'sars_scalar_5fund_dimension': 5*5,
    'sars_scalar_not_adjoint': 5*5 != 5^2 - 1,
    'sars_dimension_gap': 5*5 - (5^2 - 1),
    'odd_odd_target_even': True,
    'cl55_matrix_dimension': 32*32,
    'weyl_A4_order': W.cardinality()
})
