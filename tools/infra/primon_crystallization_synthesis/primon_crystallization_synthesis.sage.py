#!/usr/bin/env sage -python
from sage.all import QQ, prod, gap

primes = [2,3,5,7]
beta = 2
x = {p: QQ(1)/(p**beta) for p in primes}
z_boson = prod(1/(1-x[p]) for p in primes)
z_signed = prod(1-x[p] for p in primes)
z_fermion = prod(1+x[p] for p in primes)
z_second = prod(1-x[p]**2 for p in primes)
assert z_boson*z_signed == 1
assert z_fermion*z_signed == z_second
assert z_boson*z_second == z_fermion
assert int(gap.MoebiusMu(30)) == -1
assert int(gap.MoebiusMu(12)) == 0
print("SAGE_PRIMON_CRYSTALLIZATION_SYNTHESIS_OK")
print({"boson_signed": True, "fermion_second": True, "mobius_gap_crosscheck": True})
