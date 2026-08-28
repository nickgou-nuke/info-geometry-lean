#!/usr/bin/env sage
primes = [2,3,5,7,11,13]
conductors = [prod(primes[:i+1]) for i in range(len(primes))]
print("PRIME_CUMULATIVE_CYCLOTOMIC_TOWER")
for i, N in enumerate(conductors):
    K = CyclotomicField(N)
    assert K.degree() == euler_phi(N)
    assert (i == 0 or conductors[i-1] | N)
    print("stage=%d conductor=%d degree=%d unit_group_order=%d" %
          (i, N, K.degree(), euler_phi(N)))
print("STATUS=PASS")
