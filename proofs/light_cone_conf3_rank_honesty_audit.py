#!/usr/bin/env python3
"""Rank-honesty audit for the light-cone Conf_3 conjectural model.

This deliberately tests whether the naive product/cooperad candidate

    (1+t)^3 (1+t^(D-1))^2          (rank 32)

behaves like the finite-field/E-polynomial fingerprint of the actual D=4
quadric complement

    U = {(a,b) in F_q^4 x F_q^4 | q(a) q(b) q(a-b) != 0}.

Conclusion: the naive independent-product specialization is NOT equal to the
known point-count polynomial.  This does not compute Betti numbers by itself,
but it is a serious warning that the rank-32 product model is only a socketed
candidate/projection, not an established de Rham theorem.
"""

import sympy as sp


def main() -> None:
    q, u = sp.symbols("q u")

    # Actual D=4 finite-field point-count fingerprint already verified by
    # non_iso_conf3_quadric_d4_point_count.py.
    actual_count = q**2 * (q - 1) ** 2 * (q + 1) * (q**3 - 2*q**2 - q + 3)

    # One-edge quadric complement in D=4 has count q(q-1)^2(q+1), which matches
    # q^4(1-1/q)(1-1/q^2).  Thus a naive independent product rank-32 model would
    # specialize with three alpha factors of exponent 1 and two beta factors of
    # exponent 2.
    naive_rank32_count = q**8 * (1 - 1/q) ** 3 * (1 - 1/q**2) ** 2

    # The old OS-like alpha branch rank-24 similarly specializes as
    # (1 - 3/q + 2/q^2)(1 - 1/q^2)^2 q^8.
    naive_rank24_count = q**8 * (1 - 3/q + 2/q**2) * (1 - 1/q**2) ** 2

    diff32 = sp.factor(actual_count - naive_rank32_count)
    diff24 = sp.factor(actual_count - naive_rank24_count)

    assert sp.expand(diff32) != 0
    assert sp.expand(diff24) != 0

    # If the count polynomial is interpreted as compactly supported E-polynomial
    # for a polynomial-count smooth 8-fold, the ordinary E fingerprint is this.
    ordinary_E_fingerprint = sp.factor(u**8 * actual_count.subs(q, 1/u))
    naive_rank32_E = sp.factor((1 - u) ** 3 * (1 - u**2) ** 2)
    naive_rank24_E = sp.factor((1 - 3*u + 2*u**2) * (1 - u**2) ** 2)

    print("actual #U_4(F_q) =")
    sp.pprint(sp.factor(actual_count))
    print("\nnaive rank-32 product count =")
    sp.pprint(sp.factor(naive_rank32_count))
    print("actual - naive rank32 =")
    sp.pprint(diff32)
    print("\nnaive rank-24 OS count =")
    sp.pprint(sp.factor(naive_rank24_count))
    print("actual - naive rank24 =")
    sp.pprint(diff24)
    print("\nordinary E fingerprint from actual count =")
    sp.pprint(ordinary_E_fingerprint)
    print("naive rank32 E =")
    sp.pprint(naive_rank32_E)
    print("naive rank24 E =")
    sp.pprint(naive_rank24_E)
    print("\nWARNING: finite-field audit rejects both naive independent rank-32 and naive OS rank-24 specializations.")
    print("The rank-32 Lean object should be read only as a finite candidate/projection unless analytic comparison is supplied.")
    print("light_cone_conf3_rank_honesty_audit.py: audit passed (mismatch detected)")


if __name__ == "__main__":
    main()
