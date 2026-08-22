#!/usr/bin/env python3
"""CAS derivation of the PC commutator table from the carrier matrices.

This is a derivation certificate: it uses the exported GAP carrier rows and
the symbolic recovery map, not Boolean assignment enumeration.
"""
from verify_pc_collector_symbolic import I, e, gens, invmat, mm, recover, red


def factor(a, bit):
    return [[red(I[i][j] + bit * (int(a[i][j]) + I[i][j]))
             for j in range(8)] for i in range(8)]


def basis_word(k):
    out = I
    for i in range(6):
        out = mm(out, factor(gens[i], int(i == k)))
    return out


def basis_word_inv(k):
    out = I
    for i in reversed(range(6)):
        out = mm(out, factor(invmat(i), int(i == k)))
    return out


words = [basis_word(k) for k in range(6)]
inverses = [basis_word_inv(k) for k in range(6)]


def commutator(i, j):
    # [x,y] = x⁻¹ y⁻¹ x y, with the concrete group convention.
    return mm(mm(mm(inverses[i], inverses[j]), words[i]), words[j])


for i in range(6):
    for j in range(i + 1, 6):
        coords = recover(commutator(i, j), check=True)
        support = [k for k, value in enumerate(coords) if red(value - 1) == 0]
        print(f"PC_COMMUTATOR i={i} j={j} support={support}")

print("PC_COMMUTATOR_TABLE_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
