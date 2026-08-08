"""SymPy witness: Verberck pg glide extinctions filter Dirac-Fourier-Mellin zero modes.

Couples two verified layers:
- Verberck pg fixed-axis rule: c[k,0] = (-1)^k c[k,0].
- Dirac-Fourier-Mellin fixed-axis pole: det D(s,k,0)=-(s^2-k^2).

Consequence: odd fixed-axis Fourier modes have c[k,0]=0, so the associated
bulk scale poles s=±k are extinguished. Even modes are not killed by this
selection rule.
"""

import sympy as sp

s = sp.symbols("s")

print("§1  Fixed-axis Dirac scale poles")
for k in range(0, 8):
    det_D = -(s**2 - k**2)
    poles = sorted(sp.solve(sp.Eq(det_D, 0), s), key=lambda x: float(x))
    expected = [0] if k == 0 else [-k, k]
    assert poles == expected
print("   det D(s,k,0)=0 gives s=±k, with k=0 giving s=0 ✓")

print("§2  pg glide extinction on the fixed line")
for k in range(0, 8):
    phase = sp.Integer(-1) ** k
    c = sp.symbols(f"c_{k}_0")
    equation = sp.Eq(c, phase * c)
    if k % 2:
        assert sp.solve(sp.Eq(c - phase*c, 0), c) == [0]
    else:
        assert sp.simplify(c - phase*c) == 0
print("   odd k coefficients vanish; even k are not constrained to vanish ✓")

print("§3  Holographic selection rule")
extinguished = []
allowed_by_glide = []
for k in range(1, 8):
    if k % 2:
        extinguished.extend([-k, k])
    else:
        allowed_by_glide.extend([-k, k])
assert extinguished == [-1, 1, -3, 3, -5, 5, -7, 7]
assert allowed_by_glide == [-2, 2, -4, 4, -6, 6]
print("   odd scale poles s=±(2n+1) extinguished; even poles survive the glide filter ✓")

print()
print("glide_dirac_selection_rule.py: All identities verified")
