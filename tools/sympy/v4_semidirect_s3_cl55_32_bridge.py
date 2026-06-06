#!/usr/bin/env python3
"""SymPy witness for the V₄ ⋊ S₃ action on a 32-component triality bundle.

We model the ambient 96-dim space as (Cl(5,5)-style 32-component sector) × (3 triality sectors).
The 32-dimensional factor carries a concrete V₄ representation, while S₃ acts by
both sector permutation and conjugation on the V₄ generators (triality).
"""

import sympy as sp
from collections import deque


def perm_matrix(n: int, perm):
    M = sp.zeros(n, n)
    for i, j in enumerate(perm):
        M[i, j] = 1
    return M


def compose_perm(p, q):
    """Composition p ∘ q for explicit permutation tuples."""
    return tuple(q[i] for i in p)


def perm_inv(p):
    inv = [0] * len(p)
    for i, j in enumerate(p):
        inv[j] = i
    return tuple(inv)


# ------------------------------------------------------------
# 1) V₄ representation (32-dimensional seed)
# ------------------------------------------------------------
I8 = sp.eye(8)
I32 = sp.eye(32)

# 4×4 core involutions, then lifted to 32×32 by tensoring I₈.
J4 = sp.diag(-1, -1, 1, 1)
S4 = sp.diag(-1, 1, -1, 1)
JS4 = J4 * S4
I4 = sp.eye(4)

J32 = sp.kronecker_product(I8, J4)
S32 = sp.kronecker_product(I8, S4)
JS32 = sp.kronecker_product(I8, JS4)

assert J32 * J32 == I32
assert S32 * S32 == I32
assert JS32 * JS32 == I32
assert J32 * S32 == JS32
assert J32 * S32 == S32 * J32

v4_to_matrix = {
    0: I32,  # I
    1: J32,  # J
    2: S32,  # S
    3: JS32,  # JS
}


# V₄ multiplication table in labels 0=I, 1=J, 2=S, 3=JS.
def v4_mul(a: int, b: int) -> int:
    if a == 0:
        return b
    if b == 0:
        return a
    table = {
        (1, 1): 0,
        (1, 2): 3,
        (1, 3): 2,
        (2, 1): 3,
        (2, 2): 0,
        (2, 3): 1,
        (3, 1): 2,
        (3, 2): 1,
        (3, 3): 0,
    }
    return table[(a, b)]


def lift_v(v: int) -> sp.Matrix:
    return sp.kronecker_product(v4_to_matrix[v], sp.eye(3))


# ------------------------------------------------------------
# 2) S₃ data and triality action on V₄ labels
# ------------------------------------------------------------
id_perm3 = (0, 1, 2)
r3 = (1, 2, 0)  # triality 3-cycle on {0,1,2}
t3 = (1, 0, 2)  # transposition (0 1)
I3m = perm_matrix(3, id_perm3)
P3 = {id_perm3: I3m}

# Enumerate S₃ as permutation tuples.
generators3 = [r3, t3]
sector_perms = set([id_perm3])
q = deque([id_perm3])
while q:
    p = q.popleft()
    for g in generators3:
        pg = compose_perm(p, g)
        if pg not in sector_perms:
            sector_perms.add(pg)
            q.append(pg)

# Vectors in consistent order for checks.
sector_perms = sorted(sector_perms)
assert len(sector_perms) == 6


# ------------------------------------------------------------
# 3) Automorphism matrices on the 32-dim V₄ block
# ------------------------------------------------------------
# r and t act by conjugation on the 32×32 involutions.
def perm_matrix4(p):
    return perm_matrix(4, p)

r_conj4 = perm_matrix4((1, 2, 0, 3))
t_conj4 = perm_matrix4((0, 2, 1, 3))
r_conj32 = sp.kronecker_product(I8, r_conj4)
t_conj32 = sp.kronecker_product(I8, t_conj4)

A = {id_perm3: I32, r3: r_conj32, t3: t_conj32}

# Extend A by closure using composition law A[p] * A[q] = A[p∘q].
A_changed = True
while A_changed:
    A_changed = False
    for p in list(A):
        for g in generators3:
            pg = compose_perm(p, g)
            if pg not in A:
                A[pg] = A[p] * A[g]
                A_changed = True

assert len(A) == 6
assert all(p in A for p in sector_perms)


def _label_from_matrix(M: sp.Matrix) -> int:
    """Match a conjugated involution back to {I,J,S,JS} label."""
    for label, target in v4_to_matrix.items():
        if M == target:
            return label
    raise RuntimeError("matrix does not match V4 generator basis")


sector_action: dict[tuple[int, int, int], tuple[int, int, int]] = {}
for p in sector_perms:
    Ap = A[p]
    Ap_inv = Ap.inv()
    action = (
        _label_from_matrix(Ap * J32 * Ap_inv),
        _label_from_matrix(Ap * S32 * Ap_inv),
        _label_from_matrix(Ap * JS32 * Ap_inv),
    )
    assert all(a in {1, 2, 3} for a in action)
    assert len(set(action)) == 3
    sector_action[p] = action


def triality_action_label(v: int, perm) -> int:
    """Action of S₃ sector element on V₄ labels by conjugation."""
    if v == 0:
        return 0
    return sector_action[perm][v - 1]

# Explicit conjugation checks for V₄ generators.
for p in sector_perms:
    A_p = A[p]
    inv_Ap = A_p.inv()
    assert A_p * J32 * inv_Ap == v4_to_matrix[triality_action_label(1, p)]
    assert A_p * S32 * inv_Ap == v4_to_matrix[triality_action_label(2, p)]
    assert A_p * JS32 * inv_Ap == v4_to_matrix[triality_action_label(3, p)]

# S₃ representation and compatibility on 3×3 sector factors
P3 = {p: perm_matrix(3, p) for p in sector_perms}
assert all(P3[p] * P3[q] == P3[compose_perm(p, q)] for p in sector_perms for q in sector_perms)
for p in sector_perms:
    assert A[p] * A[perm_inv(p)] == I32
    assert P3[p] * P3[perm_inv(p)] == I3m

# homomorphism check for A
for p in sector_perms:
    for q in sector_perms:
        assert A[p] * A[q] == A[compose_perm(p, q)]


def lift_sigma(p) -> sp.Matrix:
    return sp.kronecker_product(A[p], P3[p])


def lift_pair(elem):
    v, p = elem
    return lift_v(v) * lift_sigma(p)

# ------------------------------------------------------------
# 4) Semidirect-group law checks on 96×96 realization
# ------------------------------------------------------------
def pair_mul(x, y):
    vx, px = x
    vy, py = y
    return (v4_mul(vx, triality_action_label(vy, px)), compose_perm(px, py))

all_elements = [(v, p) for v in range(4) for p in sector_perms]
M = {e: sp.simplify(lift_pair(e)) for e in all_elements}
for e1 in all_elements:
    for e2 in all_elements:
        lhs = M[e1] * M[e2]
        rhs = M[pair_mul(e1, e2)]
        assert lhs == rhs

# ------------------------------------------------------------
# 5) Diagnostics and core invariants
# ------------------------------------------------------------
checks = []

def chk(name, cond):
    checks.append((name, cond))
    if not cond:
        raise AssertionError(f"check failed: {name}")

identity = (0, id_perm3)
I96 = sp.eye(96)

for v in range(4):
    mat = M[(v, id_perm3)]
    chk(f"V₄ element {(v, 'I')[0]} squares to identity", mat * mat == I96)

I3m = perm_matrix(3, id_perm3)
chk("cycle permutation matrix has order 3", P3[r3] ** 3 == I3m)
chk("transposition has order 2", P3[t3] ** 2 == I3m)
chk("S₃ relation t r t = r²", P3[compose_perm(compose_perm(t3, r3), t3)] == P3[compose_perm(r3, r3)])
chk("triality 3-cycle sector element in product has order 3", M[(0, r3)] ** 3 == I96)
for p in (r3, t3):
    chk(f"V4 lift embeds at identity sector for p={p}",
        all(M[(v, p)] == M[(v, id_perm3)] * M[(0, p)] for v in range(4)))
    chk(f"S3-action transport on V4 via {p}",
        all(M[(triality_action_label(v, p), p)] == M[(0, p)] * M[(v, id_perm3)] for v in range(1, 4)))

print("\n--- V4 ⋊ S3 SymPy verification ---")
print(f"V4 states: {list(v4_to_matrix)}")
print(f"S3 states: {sector_perms}")
print(f"Semidirect elements: {len(all_elements)}")
print(f"Matrix size: {I96.rows}×{I96.cols}")
for name, cond in checks:
    print(f"{name:45}: {'✅' if cond else '❌'}")
print(f"\nOVERALL: {'True' if all(c for _, c in checks) else 'False'}")
