#!/usr/bin/env python3
"""External audit for ClebschGordanPenroseNonequilibriumSpinGraph.lean.

Checks the finite toy Clebsch--Gordan admissibility table and the
nonequilibrium Wilson-circulation classifier.  This is a witness layer only;
Lean remains the proof kernel.
"""

from fractions import Fraction

j0 = Fraction(0)
jh = Fraction(1, 2)
j1 = Fraction(1)
j3h = Fraction(3, 2)


def cg_allowed(j_a, j_b, j_c):
    """Standard finite SU(2) admissibility check for the toy labels."""
    return abs(j_a - j_b) <= j_c <= j_a + j_b and (j_a + j_b + j_c).denominator == 1


def regime_of_wilson(w):
    return "equilibriumSymmetric" if w == 0 else "nonequilibriumAsymmetric"

checks = {
    "1/2⊗1/2→0": cg_allowed(jh, jh, j0),
    "1/2⊗1/2→1": cg_allowed(jh, jh, j1),
    "1/2⊗1/2→3/2": cg_allowed(jh, jh, j3h),
    "1⊗1/2→1/2": cg_allowed(j1, jh, jh),
    "1⊗1/2→3/2": cg_allowed(j1, jh, j3h),
}

for name, value in checks.items():
    print(f"{name}: {value}")

entropy_wilson = 1 + 1 + 1
flat_wilson = 0
print("entropy Wilson =", entropy_wilson)
print("entropy regime =", regime_of_wilson(entropy_wilson))
print("flat regime =", regime_of_wilson(flat_wilson))

assert checks["1/2⊗1/2→0"] is True
assert checks["1/2⊗1/2→1"] is True
assert checks["1/2⊗1/2→3/2"] is False
assert checks["1⊗1/2→1/2"] is True
assert checks["1⊗1/2→3/2"] is True
assert entropy_wilson == 3
assert regime_of_wilson(entropy_wilson) == "nonequilibriumAsymmetric"
assert regime_of_wilson(flat_wilson) == "equilibriumSymmetric"

print("CG/Penrose nonequilibrium spin graph audit passed")
