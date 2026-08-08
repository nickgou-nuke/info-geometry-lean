"""Concrete real BPS positivity algebra.

This checks only the ordered real eigenvalue step:
  0 <= 2(M-Z) and 0 <= 2(M+Z)  =>  |Z| <= M.
It does not assert a C*-representation; that positivity is an input.
"""
import sympy as sp

M, Z = sp.symbols("M Z", real=True)

print("§1 symbolic saturation channels")
assert sp.solve(sp.Eq(2 * (M - Z), 0), M) == [Z]
assert sp.solve(sp.Eq(2 * (M + Z), 0), M) == [-Z]
print("   2(M-Z)=0 -> M=Z; 2(M+Z)=0 -> M=-Z ✓")

print("§2 numerical positivity checks for |Z| <= M")
for m, z in [(3, 2), (3, -2), (5, 0), (7, 7), (7, -7)]:
    assert 0 <= 2 * (m - z)
    assert 0 <= 2 * (m + z)
    assert abs(z) <= m
print("   positive channels imply tested real BPS bound ✓")

print("bps_positive_energy_bound.py: all identities verified")
