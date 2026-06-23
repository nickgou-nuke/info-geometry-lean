#!/usr/bin/env python3
"""Symbolic witness for the algebraic three-edge boundary packet.

This script mirrors `InfoGeometry.Topology.Amplituhedron.Boundary3Point`.
It checks only the finite nilpotent-channel calculation:

    e12 * (e12*w23 + e23*w31 + e31*w12)
      = e12*e23*w31 + e12*e31*w12

under the rewrite e12*e12 = 0, and similarly for the other two edges.
It is not a computation of an amplituhedron volume or de Rham cohomology.
"""

from __future__ import annotations

from sympy import Symbol, expand


e12 = Symbol("e12", commutative=False)
e23 = Symbol("e23", commutative=False)
e31 = Symbol("e31", commutative=False)
w12 = Symbol("omega12", commutative=False)
w23 = Symbol("omega23", commutative=False)
w31 = Symbol("omega31", commutative=False)


def reduce_nilpotents(expr):
    previous = None
    current = expand(expr)
    rules = {
        e12 * e12: 0,
        e23 * e23: 0,
        e31 * e31: 0,
    }
    while previous != current:
        previous = current
        current = expand(current.xreplace(rules))
    return current


def main() -> None:
    boundary = e12 * w23 + e23 * w31 + e31 * w12

    expected_12 = e12 * e23 * w31 + e12 * e31 * w12
    expected_23 = e23 * e12 * w23 + e23 * e31 * w12
    expected_31 = e31 * e12 * w23 + e31 * e23 * w31

    assert reduce_nilpotents(e12 * boundary - expected_12) == 0
    assert reduce_nilpotents(e23 * boundary - expected_23) == 0
    assert reduce_nilpotents(e31 * boundary - expected_31) == 0

    print("Algebraic amplituhedron boundary witness")
    print("nilpotent_edges=3")
    print("factorization_checks=3")
    print("status=ok")


if __name__ == "__main__":
    main()
