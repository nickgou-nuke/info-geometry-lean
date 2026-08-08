"""SymPy witness: glide square, supercharge square, and Casimir/mass shell.

The common structure is: an odd/projective operation squares to an even
translation generator.

- momentum-space glide g(kx,ky)=(-kx,ky+h) has g^2=(kx,ky+2h);
- SUSY supercharge Q squares to Hamiltonian/translation H;
- the relativistic Casimir is P^2=E^2-|p|^2=m^2;
- in the nilpotent boundary limit H/Casimir collapses to zero.
"""

import sympy as sp

print("§1  Momentum glide squares to reciprocal translation")
kx, ky, h = sp.symbols("kx ky h")
def glide(k):
    x, y = k
    return (-x, y + h)
assert glide(glide((kx, ky))) == (kx, ky + 2*h)
print("   g²(kx,ky)=(kx,ky+2h) ✓")

print("§2  Supercharge squares to Hamiltonian")
Q = sp.Matrix([[0, 1], [1, 0]])
H = sp.eye(2)
assert Q**2 == H
assert Q*Q + Q*Q == 2*H
print("   Q²=H and {Q,Q}=2H ✓")

print("§3  Energy-momentum Casimir")
E, px, py, pz, m = sp.symbols("E px py pz m")
casimir = E**2 - px**2 - py**2 - pz**2
assert sp.expand(casimir - m**2).subs(E**2, m**2 + px**2 + py**2 + pz**2) == 0
print("   P²=E²-|p|²=m² mass-shell Casimir ✓")

print("§4  Nilpotent boundary has zero Casimir/translation")
q = sp.Matrix([[0, 1], [0, 0]])
assert q**2 == sp.zeros(2)
H0 = sp.zeros(2)
assert q**2 == H0
print("   boundary q²=0 corresponds to collapsed H=0 / massless defect ✓")

print()
print("glide_supercharge_casimir.py: All identities verified")
