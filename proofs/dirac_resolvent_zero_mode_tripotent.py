"""SymPy witness: Fourier--Mellin Dirac zero modes and resolvent poles.

This extends the verified DiracFourierMellin layer:

    D_FM(s,k) = -sigma3 (s I - X),  X = ky sigma1 - kx sigma2.

It checks:
- exact determinant equality det(sI-X)=s^2-kx^2-ky^2;
- det(D_FM)=-det(sI-X), since det(-sigma3)=-1;
- zero-mode/singularity condition det(D_FM)=0 iff det(sI-X)=0;
- at zero boundary momentum, the only scale pole is s=0;
- this zero pole matches the zero-mode pole of the tripotent determinant
  det(sI-T)=s(s-1)(s+1).
"""

import sympy as sp

s, kx, ky = sp.symbols("s kx ky")
I = sp.I
I2 = sp.eye(2)
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma2 = sp.Matrix([[0, -I], [I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])

X = ky * sigma1 - kx * sigma2
res = s * I2 - X
D = -sigma3 * res
D_direct = -s * sigma3 + I * kx * sigma1 + I * ky * sigma2

print("§1  Dirac-resolvent factorization")
assert sp.simplify(D - D_direct) == sp.zeros(2)
print("   D_FM = -sigma3 (sI-X) ✓")

print("§2  Determinant / lightcone pole")
det_res = sp.factor(res.det())
det_D = sp.factor(D.det())
lightcone = s**2 - kx**2 - ky**2
assert det_res == lightcone
assert det_D == -lightcone
assert sp.factor(det_D + det_res) == 0
print("   det(sI-X)=s²-kx²-ky² and det(D)=-det(sI-X) ✓")

print("§3  Zero momentum gives the tripotent zero-mode scale")
zero_momentum_poles = sp.solve(sp.Eq(lightcone.subs({kx: 0, ky: 0}), 0), s)
assert zero_momentum_poles == [0]
print("   k=0 pole is exactly s=0 ✓")

print("§4  Tripotent boundary determinant shares the zero-mode pole")
T = sp.diag(1, -1, 0)
det_trip = sp.factor((s * sp.eye(3) - T).det())
assert det_trip == s * (s - 1) * (s + 1)
assert det_trip.subs(s, 0) == 0
assert det_res.subs({s: 0, kx: 0, ky: 0}) == 0
print("   tripotent defect pole s=0 matches bulk Dirac zero momentum pole ✓")

print()
print("dirac_resolvent_zero_mode_tripotent.py: All identities verified")
