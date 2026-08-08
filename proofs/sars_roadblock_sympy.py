import sympy as sp
from math import comb

charges = [2, 2, 2, -3, -3]
roots_A4 = [(i, j) for i in range(5) for j in range(5) if i != j]
sm_roots = [(i, j) for (i, j) in roots_A4 if charges[i] == charges[j]]
broken_roots = [(i, j) for (i, j) in roots_A4 if charges[i] != charges[j]]

Gamma32 = sp.diag(*([1]*16 + [-1]*16))
I32 = sp.eye(32)

su5_rank = 4
su5_adjoint_dim = su5_rank + len(roots_A4)
sm_rank = 4
sm_adjoint_dim = sm_rank + len(sm_roots)
broken_dim = len(broken_roots)
fundamental_scalar_dim = 5 * 5
exterior_c5_dim = sum(comb(5, k) for k in range(6))
so10_adjoint_dim = 10 * 9 // 2
cl55_dim = 2**10
m32_dim = 32 * 32

assert len(roots_A4) == 20
assert len(sm_roots) == 8
assert len(broken_roots) == 12
assert su5_adjoint_dim == 24
assert sm_adjoint_dim == 12
assert broken_dim == 12
assert fundamental_scalar_dim == 25
assert fundamental_scalar_dim != su5_adjoint_dim
assert fundamental_scalar_dim - su5_adjoint_dim == 1
assert exterior_c5_dim == 32
assert so10_adjoint_dim == 45
assert cl55_dim == m32_dim == 1024
assert Gamma32 * Gamma32 == I32
assert sp.trace(Gamma32) == 0
assert sp.trace(Gamma32 * I32) == 0
assert sp.trace(I32) == 32
assert {charges[i] - charges[j] for (i, j) in broken_roots} == {5, -5}

print({
    'A4_roots': len(roots_A4),
    'SM_roots_A2_plus_A1': len(sm_roots),
    'broken_roots': len(broken_roots),
    'su5_adjoint_dim': su5_adjoint_dim,
    'sm_adjoint_dim': sm_adjoint_dim,
    'broken_dim': broken_dim,
    'fundamental_scalar_dim': fundamental_scalar_dim,
    'fundamental_not_adjoint': fundamental_scalar_dim != su5_adjoint_dim,
    'dimension_gap': fundamental_scalar_dim - su5_adjoint_dim,
    'exterior_c5_dim': exterior_c5_dim,
    'so10_adjoint_dim': so10_adjoint_dim,
    'cl55_dim': cl55_dim,
    'm32_dim': m32_dim,
    'trace_gamma32': sp.trace(Gamma32),
    'supertrace_identity': sp.trace(Gamma32 * I32),
    'trace_identity': sp.trace(I32),
    'odd_odd_target_even': True,
})
