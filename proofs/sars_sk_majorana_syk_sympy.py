import sympy as sp
from functools import reduce

I2 = sp.eye(2)
X = sp.Matrix([[0, 1], [1, 0]])
Y = sp.Matrix([[0, -sp.I], [sp.I, 0]])
Z = sp.Matrix([[1, 0], [0, -1]])

def kron_all(ms):
    return reduce(lambda a,b: sp.kronecker_product(a,b), ms)

def dla_dim_syk(n):
    return 2**(2*n - 1) - 2

def dla_dim_sk(L):
    return 2*(4**(L-1) - 1)

def pool_size_sk(L):
    return L * (L - 1)

def pool_size_syk(n):
    return n + 3 * n * (n - 1) // 2

def majorana_count(n):
    return 2*n

def hilbert_dim(n):
    return 2**n

def matrix_alg_dim(n):
    return hilbert_dim(n)**2

def cl_balanced_dim(n):
    return 2**(2*n)

def jw_majoranas(k, n):
    prefix = [Z]*(k-1)
    suffix = [I2]*(n-k)
    return kron_all(prefix + [X] + suffix), kron_all(prefix + [Y] + suffix)

def anticomm(A,B):
    return sp.simplify(A*B + B*A)

assert dla_dim_syk(4) == 126
assert dla_dim_sk(8) == 32766
assert pool_size_sk(8) == 56
assert pool_size_syk(4) == 22
assert majorana_count(4) == 8
assert hilbert_dim(10) == 1024
assert matrix_alg_dim(5) == 1024
assert cl_balanced_dim(5) == 1024
assert 32*32 == 2**10

chi1, chi2 = jw_majoranas(1, 2)
chi3, chi4 = jw_majoranas(2, 2)
for A in [chi1, chi2, chi3, chi4]:
    assert anticomm(A,A) == 2*sp.eye(4)
for A,B in [(chi1,chi2),(chi1,chi3),(chi1,chi4),(chi2,chi3),(chi2,chi4),(chi3,chi4)]:
    assert anticomm(A,B) == sp.zeros(4)

edges = ['has_pool_size','has_dla_dimension','embeds_by','realizes_cl55_block','scales_as']
print({'dla_dim_syk_4': dla_dim_syk(4), 'dla_dim_sk_8': dla_dim_sk(8), 'pool_sk_8': pool_size_sk(8), 'pool_syk_4': pool_size_syk(4), 'majoranas_n4': majorana_count(4), 'cl55_matrix_dim': 32*32, 'jw_clifford_sample': True, 'edges': len(edges)})
