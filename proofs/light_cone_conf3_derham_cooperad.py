#!/usr/bin/env python3
"""SymPy audit for the light-cone Conf_3 finite de Rham/cooperad candidate.

This is not a proof of the analytic de Rham comparison.  It checks the finite
rank/Poincare-polynomial fingerprints and the elementary Jacobian witness that
q(a), q(b), q(a-b) can meet with independent differentials in D=4.
"""

import sympy as sp


def product_poincare(D: int):
    t = sp.Symbol("t")
    return sp.expand((1 + t) ** 3 * (1 + t ** (D - 1)) ** 2)


def os_alpha_poincare(D: int):
    t = sp.Symbol("t")
    return sp.expand((1 + 3 * t + 2 * t**2) * (1 + t ** (D - 1)) ** 2)


def q(v):
    return sum(x * x for x in v)


def d4_jacobian_rank_witness():
    I = sp.I
    a_vars = sp.symbols("a0:4")
    b_vars = sp.symbols("b0:4")
    a = [1, I, 0, 0]
    b = [0, 0, 1, I]
    polys = [q(a_vars), q(b_vars), q([a_vars[i] - b_vars[i] for i in range(4)])]
    subs = {a_vars[i]: a[i] for i in range(4)}
    subs.update({b_vars[i]: b[i] for i in range(4)})
    values = [sp.simplify(p.subs(subs)) for p in polys]
    J = sp.Matrix([[sp.diff(p, v) for v in (*a_vars, *b_vars)] for p in polys])
    rank = J.subs(subs).rank()
    return values, rank


def collapse12(edge: str) -> str:
    return {"12": "inner", "13": "outer", "23": "outer"}[edge]


def main():
    t = sp.Symbol("t")
    for D in (4, 6, 8, 10):
        P = product_poincare(D)
        Q = os_alpha_poincare(D)
        assert sp.simplify(P.subs(t, 1) - 32) == 0
        assert sp.simplify(Q.subs(t, 1) - 24) == 0
        print(f"D={D}")
        print(f"  product/Leray: {P}")
        print(f"  OS-alpha:      {Q}")

    values, rank = d4_jacobian_rank_witness()
    assert values == [0, 0, 0]
    assert rank == 3
    assert [collapse12(e) for e in ("12", "13", "23")] == ["inner", "outer", "outer"]
    print("D=4 triple intersection witness: q values", values, "Jacobian rank", rank)
    print("cooperad split {1,2}|{3}: 12->inner, 13/23->outer")
    print("light_cone_conf3_derham_cooperad.py: finite audit passed")


if __name__ == "__main__":
    main()
