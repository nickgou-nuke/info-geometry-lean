"""Carrier-aligned CAS audit for the six-step residual peel.

This is an external audit only.  It does not assert a Lean theorem.  The
matrix convention is the repository convention: a PC word is the ordered
left-to-right product of the six exported PC matrices, while the Lean
automorphism multiplication is contravariant on matrices.  The script checks
the important boundary condition: the six pivots remove a left B-factor, but
they do not remove a right B-factor.  Thus the proposed theorem
`fullPeel f ∈ W` is false for the current one-sided `fullPeel`.
"""

import itertools
import numpy as np

from verify_sylow_pc_closure import s_gens


I = np.eye(8, dtype=np.int64)


def mm(a, b):
    return (a @ b) % 2


def word(bits):
    out = I.copy()
    for bit, gen in zip(bits, s_gens):
        if bit:
            out = mm(out, gen)
    return out


def peel(m):
    """Return (bits, residual), exactly matching G2TwoPCRecovery.fullPeel."""
    p0, p1, p2, p3, p4, p5 = s_gens
    q1 = mm(p5, p1)
    q2 = mm(p5, p2)
    bits = []

    b0 = int(m[2, 7])
    bits.append(b0)
    # `autMatrix (q * f) = autMatrix f * autMatrix q`.
    m = mm(m, p0) if b0 else m

    b1 = int(m[3, 2])
    bits.append(b1)
    m = mm(m, q1) if b1 else m

    b2 = int(m[3, 7])
    bits.append(b2)
    m = mm(m, q2) if b2 else m

    b4 = int(m[6, 2])
    b3 = int(m[4, 3]) ^ b4
    bits.extend([b3, b4])
    m = mm(m, p4) if b4 else m
    m = mm(m, p3) if b3 else m

    b5 = int(m[4, 2])
    bits.append(b5)
    m = mm(m, p5) if b5 else m
    return tuple(bits), m


swap01 = np.array([
    [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
    [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0],
    [0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0],
    [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,0,1]], dtype=np.int64)
cycle012 = np.array([
    [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
    [0,0,0,0,1,0,0,0], [0,0,1,0,0,0,0,0],
    [0,0,0,1,0,0,0,0], [0,0,0,0,0,0,0,1],
    [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0]], dtype=np.int64)
swap_cartan = np.array([
    [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0],
    [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0],
    [0,0,0,0,0,0,0,1], [0,0,1,0,0,0,0,0],
    [0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0]], dtype=np.int64)


def generated_weyl():
    c = mm(swap_cartan, cycle012)
    return [mm(swap01 if refl else I, np.linalg.matrix_power(c, k) % 2)
            for refl in (0, 1) for k in range(6)]


def main():
    b_list = [word(bits) for bits in itertools.product((0, 1), repeat=6)]
    n_list = generated_weyl()
    generated = {mm(mm(b1, w), b2).tobytes()
                 for b1 in b_list for w in n_list for b2 in b_list}
    assert len(generated) == 12096
    n_set = {w.tobytes() for w in n_list}
    # A concrete right-B factor is enough to expose the one-sided nature of
    # fullPeel.  This is a counterexample to residual Weyl membership, not a
    # failed implementation test.
    f = mm(n_list[1], s_gens[0])
    bits, residual = peel(f)
    assert residual.tobytes() not in n_set
    print("FULL_PEEL_RESIDUAL_Weyl=FALSE")
    print("COUNTEREXAMPLE=f=w(1)*pc0")
    print("EXTRACTED_BITS=", bits)
    print("RESIDUAL_NOT_IN_Weyl=PASS")
    print("GENERATED_BN_CARD=12096")
    print("RESIDUAL_Weyl_CARD=12")


if __name__ == "__main__":
    main()
