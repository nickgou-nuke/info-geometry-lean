#!/usr/bin/env python3
"""q-Fock Gram matrices for the golden parameter q=φ⁻¹.

For orthonormal one-particle labels, the n-particle q-Fock inner product is
  <i_1...i_n, j_1...j_n> = Σ_{σ∈S_n, i_k = j_{σ(k)} ∀k} q^inv(σ).
This checks the n=2 and n=3 binary sectors symbolically/numerically.
"""

from itertools import product, permutations
import sympy as sp

sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
q = 1 / phi


def inv_count(p):
    return sum(1 for a in range(len(p)) for b in range(a + 1, len(p)) if p[a] > p[b])


def q_inner(u, v):
    n = len(u)
    total = 0
    for sig in permutations(range(n)):
        if all(u[k] == v[sig[k]] for k in range(n)):
            total += q ** inv_count(sig)
    return sp.simplify(total)


def gram(n):
    words = list(product([0, 1], repeat=n))
    G = sp.Matrix([[q_inner(u, v) for v in words] for u in words])
    return words, G

for n in [2, 3]:
    print(f"§ q-Fock binary Gram matrix, n={n}")
    words, G = gram(n)
    print("basis:", ["".join(map(str, w)) for w in words])
    assert G == G.T
    minors = []
    for k in range(1, G.rows + 1):
        minors.append(sp.simplify(G[:k, :k].det()))
    numeric_eigs = [ev.evalf() for ev in G.eigenvals().keys()]
    print("leading principal minors:", [sp.simplify(m) for m in minors])
    assert all(float(m.evalf()) > 0 for m in minors)
    print("eigenvalues:", numeric_eigs)
    assert all(float(ev) > 0 for ev in numeric_eigs)
    print(f"positive definite for q=φ⁻¹, n={n} ✓\n")

print("golden_fock_gram.py: All q-Fock Gram checks passed")
