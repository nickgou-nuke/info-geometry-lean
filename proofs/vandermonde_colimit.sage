k = 10
P = Primes()
primes = [P.unrank(i) for i in range(k)]

N = 50
def is_smooth(x, primes):
    if x == 1:
        return True
    f = factor(x)
    return all(p in primes for p, _ in f)

elements = [i for i in range(1, N+1) if is_smooth(i, primes)]
n = len(elements)

V = matrix(QQ, n, n, lambda i, j: 1 if elements[j] % elements[i] == 0 else 0)
V_inv = V.inverse()

M = matrix(QQ, n, n, lambda i, j: moebius(elements[j] // elements[i]) if elements[j] % elements[i] == 0 else 0)

assert V_inv == M
print("Vandermonde inverse perfectly matches Möbius inversion over the truncated multiplicative monoid.")
