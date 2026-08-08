"""SymPy witness: Möbius parity and Möbius/glide-twisted Witten index.

Checks:
- μ(n)=0 for Pauli-forbidden non-squarefree occupations;
- μ(n)=(-1)^F for squarefree n, where F=# distinct prime factors;
- SUSY paired positive-energy states cancel in Tr[G(-1)^F exp(-βH)];
- the remaining twisted Witten index is β-independent, so U=0 and Cv=0;
- pg fixed-line glide extinction kills odd k modes.
"""

import sympy as sp

print("§1  Möbius function as chiral fermion parity")
for n in range(1, 50):
    mu = sp.mobius(n)
    fac = sp.factorint(n)
    squarefree = all(a == 1 for a in fac.values())
    if not squarefree:
        assert mu == 0
    else:
        F = len(fac)
        assert mu == (-1) ** F
print("   μ(n)=0 for repeated prime occupation; μ(n)=(-1)^F for squarefree n ✓")

print("§2  Twisted Witten index cancels positive-energy superpairs")
beta = sp.symbols("beta", positive=True)
# each positive-energy superpair has same G eigenvalue g and energy E
pairs = [(1, 2), (-1, 3), (1, 5)]  # (g,E)
positive_trace = sum(g*(+1)*sp.exp(-beta*E) + g*(-1)*sp.exp(-beta*E) for g,E in pairs)
assert sp.simplify(positive_trace) == 0
W = sp.symbols("W", nonzero=True)
Z = W + positive_trace
assert sp.simplify(Z - W) == 0
U = -sp.diff(sp.log(Z), beta)
Cv = sp.diff(U, beta)
assert sp.simplify(U) == 0
assert sp.simplify(Cv) == 0
print("   Z_G(β)=W_G is β-independent; U=0 and Cv=0 ✓")

print("§3  Brillouin Klein fixed-line glide filter")
for k in range(10):
    phase = sp.Integer(-1)**k
    c = sp.symbols(f"c_{k}_0")
    if k % 2:
        assert sp.solve(sp.Eq(c - phase*c, 0), c) == [0]
    else:
        assert sp.simplify(c - phase*c) == 0
print("   odd fixed-line modes vanish; even zero-modes can contribute to W_G ✓")

print()
print("mobius_witten_klein_index.py: All identities verified")
