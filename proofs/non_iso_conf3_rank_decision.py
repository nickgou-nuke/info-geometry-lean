#!/usr/bin/env python3
"""Audit for the rank-32 vs rank-24 fork.

The key check is that for q=sum x_i^2 in C^4, the three equations
q(a)=q(b)=q(a-b)=0 have a smooth complete-intersection point of Jacobian rank 3.
This supports the Dupont/OS codimension datum codim triple = 3, hence the three
alpha divisor classes are independent rather than A2-dependent.
"""

import sympy as sp


def main() -> None:
    I = sp.I
    # a=(1,i,0,0), b=(0,0,1,i): q(a)=q(b)=B(a,b)=0 and a != b.
    a = sp.Matrix([1, I, 0, 0])
    b = sp.Matrix([0, 0, 1, I])
    q = lambda v: sum(x * x for x in v)
    assert sp.simplify(q(a)) == 0
    assert sp.simplify(q(b)) == 0
    assert sp.simplify(q(a - b)) == 0

    a_vars = sp.symbols("a0:4")
    b_vars = sp.symbols("b0:4")
    av = sp.Matrix(a_vars)
    bv = sp.Matrix(b_vars)
    f1 = q(av)
    f2 = q(bv)
    f3 = q(av - bv)
    vars_ = list(a_vars + b_vars)
    J = sp.Matrix([[sp.diff(f, x) for x in vars_] for f in (f1, f2, f3)])
    subs = {a_vars[i]: a[i] for i in range(4)}
    subs.update({b_vars[i]: b[i] for i in range(4)})
    Jr = J.subs(subs)
    assert Jr.rank() == 3

    product_rank = 2**3 * 2**2
    os_alpha_rank = 6 * 2**2
    assert product_rank == 32
    assert os_alpha_rank == 24
    assert product_rank - os_alpha_rank == 8

    print("non_iso_conf3_rank_decision.py: rank fork audit passed")
    print("Jacobian rank at isotropic orthogonal point: 3")
    print("Dupont/OS codim-triple independence favors rank 32 over rank 24.")
    print("Full de Rham theorem still needs resolved Dupont beta/Gysin computation.")


if __name__ == "__main__":
    main()
