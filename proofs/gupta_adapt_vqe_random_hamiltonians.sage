from sage.all import *

Q = QQ

def pair_count(n):
    return ZZ(n * (n - 1) // 2)

def four_body_count(N):
    return ZZ(N * (N - 1) * (N - 2) * (N - 3) // 24)

assert four_body_count(20) == 4845
assert 20 // 2 == 10
assert 9 * 20 == 180
assert Q(4845 - 180) / 4845 == Q(311) / 323

R = PolynomialRing(QQ, ["N"])
N = R.gen()
sparse_probability = 24 * (N**3 / 24) / N**3
assert sparse_probability == 1

def sk_pool_size(L):
    return 2 * pair_count(L)

def syk_pool_size(n):
    return n + 3 * pair_count(n)

assert sk_pool_size(18) == 306
assert syk_pool_size(10) == 145
assert pair_count(18) + 18 == 171
assert 2 ** (20 // 2) == 1024
assert abs(Q(275) / 100 - Q(278) / 100) == Q(3) / 100
assert Q(9936) / 10000 >= Q(993) / 1000
assert Q(9966) / 10000 >= Q(993) / 1000
assert 2 ** (2 * 10 - 1) - 2 == 524286
assert 2 * (4 ** (4 - 1) - 1) == 126

print({
    "dense_SYK_terms_N20": four_body_count(20),
    "sparse_SYK_terms_ks9_N20": 9 * 20,
    "removed_ratio": Q(311) / 323,
    "SK_pool_L18": sk_pool_size(18),
    "SYK_pool_n10": syk_pool_size(10),
    "hilbert_dim_N20": 2 ** (20 // 2),
})
