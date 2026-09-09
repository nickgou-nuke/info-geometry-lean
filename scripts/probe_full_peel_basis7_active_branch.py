"""Discovery-only probe for the active final peel branch.

The output is CAS evidence for shaping native Lean readback lemmas.  It is
not imported as a theorem and does not establish any Lean proposition.
"""

from collections import Counter

from verify_flag_stabilizer_full_peel_cas import subgroup
from verify_full_peel_residual_cas import mm, peel, s_gens


def basis(i):
    v = [0] * 8
    v[i] = 1
    return v


def row_image(m, v):
    return tuple(int(x) for x in (m @ v) % 2)


def main():
    import numpy as np

    elements = subgroup([s_gens[0], s_gens[1], s_gens[2], s_gens[4]])
    e2 = np.array(basis(2), dtype=np.int64)
    e7 = np.array(basis(7), dtype=np.int64)
    transformed = np.array([0, 0, 0, 0, 0, 1, 0, 1], dtype=np.int64)
    active = Counter()
    for element in elements:
        bits, residual = peel(element)
        if bits[5] == 1:
            p0, p1, p2, p3, p4, p5 = s_gens
            q1 = mm(p5, p1)
            q2 = mm(p5, p2)
            m = mm(element, p0) if bits[0] else element
            m = mm(m, q1) if bits[1] else m
            m = mm(m, q2) if bits[2] else m
            b4 = bits[4]
            b3 = bits[3]
            m = mm(m, p4) if b4 else m
            m = mm(m, p3) if b3 else m
            active[(tuple(bits), row_image(residual, e2),
                    row_image(m, transformed), row_image(m, e7),
                    row_image(residual, e7))] += 1
    print("ACTIVE_FINAL_PEEL_COUNT=", sum(active.values()))
    print("ACTIVE_FINAL_PEEL_CASES=", len(active))
    for case, count in sorted(active.items()):
        print("ACTIVE_CASE", case, "COUNT", count)


if __name__ == "__main__":
    main()
