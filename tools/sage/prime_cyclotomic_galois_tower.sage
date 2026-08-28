# Prime cyclotomic Galois tower certificate generator
# External evidence only: Lean independently reproves every exported arithmetic fact.

primes = [2, 3, 5, 7, 11, 13]
conductors = []
N = ZZ(1)
for p in primes:
    N *= p
    conductors.append(N)

print("prime,conductor,phi")
for p, N in zip(primes, conductors):
    K = CyclotomicField(N)
    assert K.degree() == euler_phi(N)
    print(f"{p},{N},{euler_phi(N)}")

# Genuine nesting: if N | M then zeta_N maps to zeta_M^(M/N).
for N, M in zip(conductors[:-1], conductors[1:]):
    assert M % N == 0
    KN = CyclotomicField(N)
    KM = CyclotomicField(M)
    zN = KN.gen()
    zM = KM.gen()
    image = zM^(M // N)
    assert image^N == 1
    # The relation records the canonical cyclotomic embedding generator image.
    print(f"embed,{N},{M},power,{M//N}")
