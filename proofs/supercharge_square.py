"""SymPy witness: supercharges square to the Hamiltonian/translation atom.

In the minimal N=1 spatial SUSY atom, an odd generator Q satisfies
    {Q,Q}=2H,
so equivalently Q^2=H.
We use Q=sigma_x, H=I.  A nilpotent boundary supercharge q has q^2=0,
representing the collapsed zero-energy defect sector.
"""

import sympy as sp

print("§1  osp/N=1 supercharge square")
Q = sp.Matrix([[0, 1], [1, 0]])
H = sp.eye(2)
assert Q**2 == H
assert Q*Q + Q*Q == 2*H
print("   Q²=H and {Q,Q}=2H ✓")

print("§2  Chiral parity anticommutes with supercharge")
F = sp.Matrix([[1, 0], [0, -1]])
assert F*Q + Q*F == sp.zeros(2)
assert F**2 == H
print("   (-1)^F anticommutes with Q and squares to 1 ✓")

print("§3  Nilpotent boundary supercharge")
q = sp.Matrix([[0, 1], [0, 0]])
assert q**2 == sp.zeros(2)
assert q*q + q*q == sp.zeros(2)
print("   collapsed boundary q²=0 and {q,q}=0 ✓")

print()
print("supercharge_square.py: All identities verified")
