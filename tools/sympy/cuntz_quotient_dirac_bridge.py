#!/usr/bin/env python3
"""Finite quotient CuntzN/Hodge-Dirac bridge mirror.

A genuine finite-dimensional matrix model of O_n for n>1 cannot satisfy the full
Cuntz relations.  This script mirrors the kernel-checked Lean bridge in the
exact n=1 finite case: S*=S=1, D=S+S*, P=SS*, with D self-adjoint and P²=P.
"""

import sympy as sp


def main():
    S = sp.Matrix([[1]])
    Sdag = S.conjugate().T
    D = S + Sdag
    P = S * Sdag

    assert Sdag * S == sp.eye(1)
    assert S * Sdag == sp.eye(1)
    assert D == sp.Matrix([[2]])
    assert D.conjugate().T == D
    assert P * P == P

    print("finite n=1 Cuntz quotient Dirac bridge checks ok")


if __name__ == "__main__":
    main()
