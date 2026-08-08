def dla_dim_syk(n):
    return 2^(2*n - 1) - 2

def dla_dim_sk(L):
    return 2*(4^(L-1) - 1)

def pool_size_sk(L):
    return L*(L-1)

def pool_size_syk(n):
    return n + 3*n*(n-1)//2

def majorana_count(n):
    return 2*n

def hilbert_dim(n):
    return 2^n

def matrix_alg_dim(n):
    return hilbert_dim(n)^2

def cl_balanced_dim(n):
    return 2^(2*n)

assert dla_dim_syk(4) == 126
assert dla_dim_sk(8) == 32766
assert pool_size_sk(8) == 56
assert pool_size_syk(4) == 22
assert majorana_count(4) == 8
assert hilbert_dim(10) == 1024
assert matrix_alg_dim(5) == 1024
assert cl_balanced_dim(5) == 1024
assert 32*32 == 2^10

W_A4 = WeylGroup(['A',4], prefix='s')
assert W_A4.order() == 120
S5 = SymmetricGroup(5)
assert S5.order() == 120
edges = ['has_pool_size','has_dla_dimension','embeds_by','realizes_cl55_block','scales_as']
print({'dla_dim_syk_4': dla_dim_syk(4), 'dla_dim_sk_8': dla_dim_sk(8), 'pool_sk_8': pool_size_sk(8), 'pool_syk_4': pool_size_syk(4), 'majoranas_n4': majorana_count(4), 'cl55_matrix_dim': 32*32, 'W_A4_order': W_A4.order(), 'S5_order': S5.order(), 'edges': len(edges)})
