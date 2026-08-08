import sympy as sp

Q = sp.Rational

def pair_count(n):
    return n * (n - 1) // 2

def four_body_count(N):
    return N * (N - 1) * (N - 2) * (N - 3) // 24

assert four_body_count(20) == 4845
assert 20 // 2 == 10
assert 9 * 20 == 180
assert Q(4845 - 180, 4845) == Q(311, 323)

N, ks = sp.symbols("N ks", nonzero=True)
def sparse_probability(ks0, N0):
    return sp.factor(24 * ks0 / N0**3)

assert sp.simplify(sparse_probability(N**3 / 24, N) - 1) == 0

def sk_pool_size(L):
    return 2 * pair_count(L)

def syk_pool_size(n):
    return n + 3 * pair_count(n)

assert sk_pool_size(18) == 306
assert syk_pool_size(10) == 145
assert pair_count(18) + 18 == 171

def odd_y_allowed(ys):
    return ys % 2 == 1

assert odd_y_allowed(1)
assert not odd_y_allowed(2)

def relative_energy_error(exact, adapt):
    return sp.factor((exact - adapt) / exact)

E = sp.symbols("E", nonzero=True)
assert sp.simplify(relative_energy_error(E, E)) == 0

assert 2 ** (20 // 2) == 1024

dense_entropy_N20 = Q(275, 100)
sparse_entropy_N20 = Q(278, 100)
assert abs(dense_entropy_N20 - sparse_entropy_N20) == Q(3, 100)

dense_fidelity_N20 = Q(9936, 10000)
sparse_fidelity_N20 = Q(9966, 10000)
assert dense_fidelity_N20 >= Q(993, 1000)
assert sparse_fidelity_N20 >= Q(993, 1000)

def dense_syk_dla_dim(n):
    return 2 ** (2 * n - 1) - 2

def sk_dla_dim(L):
    return 2 * (4 ** (L - 1) - 1)

assert dense_syk_dla_dim(10) == 524286
assert sk_dla_dim(4) == 126

print({
    "dense_SYK_terms_N20": four_body_count(20),
    "sparse_SYK_terms_ks9_N20": 9 * 20,
    "removed_ratio": Q(311, 323),
    "SK_pool_L18": sk_pool_size(18),
    "SYK_pool_n10": syk_pool_size(10),
    "hilbert_dim_N20": 2 ** (20 // 2),
})
