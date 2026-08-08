#!/usr/bin/env python3
"""SymPy witness for the chiral cone alphabet {N_+, N_-, s_+, s_-, s_3}.

The Lean proof kernel is `ChiralConeAlgebraFinality.lean`; this script audits
the same finite `M_2(C)` matrix identities:

* nilpotent transitions s_+^2=s_-^2=0;
* determinant-null transitions det(s_±)=0;
* chiral projectors N_+=s_+s_-, N_-=s_-s_+;
* completeness and Pauli exclusion N_++N_-=I, N_+N_-=0;
* parity axis s_3=N_+-N_-;
* Lie relations [s_3,s_±]=±2s_±;
* normalized GNS trace tau(N_+)=tau(N_-)=1/2;
* determinant barrier -log det(X) diverges at a nilpotent cone point.
"""

import sympy as sp


def commutator(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b - b * a


def tau(a: sp.Matrix) -> sp.Expr:
    return sp.trace(a) / 2


def main() -> None:
    s_plus = sp.Matrix([[0, 1], [0, 0]])
    s_minus = sp.Matrix([[0, 0], [1, 0]])
    identity = sp.eye(2)
    zero = sp.zeros(2)

    n_plus = s_plus * s_minus
    n_minus = s_minus * s_plus
    s3 = n_plus - n_minus

    assert s_plus**2 == zero
    assert s_minus**2 == zero
    assert s_plus.det() == 0
    assert s_minus.det() == 0

    assert n_plus == sp.Matrix([[1, 0], [0, 0]])
    assert n_minus == sp.Matrix([[0, 0], [0, 1]])
    assert n_plus**2 == n_plus
    assert n_minus**2 == n_minus
    assert n_plus + n_minus == identity
    assert n_plus * n_minus == zero
    assert n_minus * n_plus == zero

    assert s3 == sp.Matrix([[1, 0], [0, -1]])
    assert s3**2 == identity
    assert commutator(s3, s_plus) == 2 * s_plus
    assert commutator(s3, s_minus) == -2 * s_minus
    assert s_plus * s_minus + s_minus * s_plus == identity
    assert s_plus * s_minus - s_minus * s_plus == s3

    assert tau(n_plus) == sp.Rational(1, 2)
    assert tau(n_minus) == sp.Rational(1, 2)
    assert tau(s3) == 0
    assert tau(identity) == 1

    # Barrier check: X(ε)=s_+ + εI leaves the determinant zero locus for ε≠0,
    # and -log det X diverges as ε -> 0+.
    eps = sp.symbols("eps", positive=True)
    x_eps = s_plus + eps * identity
    det_x_eps = sp.factor(x_eps.det())
    barrier = -sp.log(det_x_eps)
    assert det_x_eps == eps**2
    assert sp.limit(barrier, eps, 0, dir="+") == sp.oo

    print("s_plus =")
    sp.pprint(s_plus)
    print("s_minus =")
    sp.pprint(s_minus)
    print("N_plus = s_plus*s_minus =")
    sp.pprint(n_plus)
    print("N_minus = s_minus*s_plus =")
    sp.pprint(n_minus)
    print("s3 = N_plus-N_minus =")
    sp.pprint(s3)
    print("[s3,s_plus] =")
    sp.pprint(commutator(s3, s_plus))
    print("[s3,s_minus] =")
    sp.pprint(commutator(s3, s_minus))
    print("tau(N_plus), tau(N_minus), tau(s3) =", tau(n_plus), tau(n_minus), tau(s3))
    print("det(s_plus + eps*I) =", det_x_eps)
    print("-log det barrier limit at apex =", sp.limit(barrier, eps, 0, dir="+"))
    print("chiral_cone_algebra_finality.py: finite audit passed")


if __name__ == "__main__":
    main()
