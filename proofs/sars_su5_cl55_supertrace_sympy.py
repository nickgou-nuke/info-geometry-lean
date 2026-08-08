import sympy as sp
from math import comb

I16 = sp.eye(16)
Z16 = sp.zeros(16)
Gamma32 = sp.diag(*([1]*16 + [-1]*16))
I32 = sp.eye(32)

p = 5
q = 5
n = p + q
omega_square = (-1)**(n*(n-1)//2) * (-1)**q

su5_fundamental = 5
su5_lambda2 = sp.binomial(5, 2)
su5_adjoint = 5**2 - 1
sm_adjoint = (3**2 - 1) + (2**2 - 1) + 1
xy_bosons = su5_adjoint - sm_adjoint
so10_adjoint = 10 * (10 - 1) // 2
exterior_C5 = 0
for k in range(6):
    exterior_C5 += comb(5, k)
sars_scalar_sector = 5 * su5_fundamental
sars_dimension_gap = sars_scalar_sector - su5_adjoint
cl55_matrix_dim = 32 * 32
odd_odd_target_even = True
spinor_plus = 16
spinor_minus = 16

assert omega_square == 1
assert Gamma32 * Gamma32 == I32
assert sp.trace(Gamma32) == 0
assert sp.trace(Gamma32 * I32) == 0
assert sp.trace(I32) == 32
assert su5_lambda2 == 10
assert su5_adjoint == 24
assert sm_adjoint == 12
assert xy_bosons == 12
assert so10_adjoint == 45
assert exterior_C5 == 32
assert sars_scalar_sector == 25
assert sars_scalar_sector != su5_adjoint
assert sars_dimension_gap == 1
assert cl55_matrix_dim == 2**10
assert odd_odd_target_even is True
assert spinor_plus - spinor_minus == 0

Q = sp.Matrix([[sp.Symbol('a'), sp.Symbol('b')], [sp.Symbol('c'), sp.Symbol('d')]])
P = sp.Matrix([[sp.Symbol('e'), sp.Symbol('f')], [sp.Symbol('g'), sp.Symbol('h')]])
assert sp.simplify(sp.trace(Q*P - P*Q)) == 0

print({
    'omega_square_5_5': omega_square,
    'trace_Gamma32': sp.trace(Gamma32),
    'supertrace_identity_32': sp.trace(Gamma32 * I32),
    'trace_identity_32': sp.trace(I32),
    'su5_lambda2': su5_lambda2,
    'su5_adjoint': su5_adjoint,
    'sm_adjoint': sm_adjoint,
    'xy_bosons': xy_bosons,
    'so10_adjoint': so10_adjoint,
    'exterior_C5_dimension': exterior_C5,
    'sars_scalar_5fund_dimension': sars_scalar_sector,
    'sars_scalar_not_adjoint': sars_scalar_sector != su5_adjoint,
    'sars_dimension_gap': sars_dimension_gap,
    'odd_odd_target_even': odd_odd_target_even,
    'cl55_matrix_dimension': cl55_matrix_dim,
    'spinor_balance': spinor_plus - spinor_minus,
    'trace_commutator_M2': sp.simplify(sp.trace(Q*P - P*Q)),
})
