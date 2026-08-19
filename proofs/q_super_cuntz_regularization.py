#!/usr/bin/env python3
"""Finite audit for q-super-Cuntz regularization deferred_interface.

Checks the theorem-proved finite content:
  eta = PB - PF = (-1)^F,
  eta^2 = I,
  STr(X)=Tr(eta X)=X00-X11,
  Cayley(T) is unitary and DKT/superparity adjoint agrees on the diagonal stage.
Also evaluates a root-of-unity q-super-commutator witness at q=exp(i*pi/4).
"""

import sympy as sp


def dagger(A):
    return A.conjugate().T


def main():
    I2 = sp.eye(2)
    PB = sp.diag(1, 0)
    PF = sp.diag(0, 1)
    eta = PB - PF

    assert eta == sp.diag(1, -1)
    assert eta * eta == I2
    assert dagger(eta) == eta

    x00, x01, x10, x11 = sp.symbols("x00 x01 x10 x11", complex=True)
    X = sp.Matrix([[x00, x01], [x10, x11]])
    supertrace = sp.trace(eta * X)
    assert sp.simplify(supertrace - (x00 - x11)) == 0
    assert sp.trace(eta * I2) == 0
    assert sp.trace(eta * eta) == 2

    lam = sp.Symbol("lam", real=True, positive=True)
    T = sp.diag(lam, 2 * lam)
    U = (T - sp.I * I2) * (T + sp.I * I2).inv()

    def dkt(A):
        return eta * dagger(A) * eta

    assert sp.simplify(U * dagger(U) - I2) == sp.zeros(2)
    assert sp.simplify(dkt(U) - dagger(U)) == sp.zeros(2)
    assert sp.simplify(U * dkt(U) - I2) == sp.zeros(2)

    q = sp.exp(sp.I * sp.pi / 4)
    S_b = sp.Matrix([[0, 1], [0, 0]])
    S_f = sp.Matrix([[0, 0], [1, 0]])
    bosonic_q_comm = dagger(S_b) * S_b - q * (S_b * dagger(S_b))
    fermionic_q_comm = dagger(S_f) * S_f + q * (S_f * dagger(S_f))

    print("q_super_cuntz_regularization.py: finite witnesses passed")
    print("eta = PB - PF =")
    sp.pprint(eta)
    print("STr(X)=X00-X11; STr(I)=0; STr(eta)=2")
    print("q = exp(i*pi/4) =", q)
    print("bosonic q-commutator witness:")
    sp.pprint(bosonic_q_comm)
    print("fermionic q-anticommutator witness:")
    sp.pprint(fermionic_q_comm)
    print("Cayley stage: U†U=I and DKT(U)=U†")
    print("Root-of-unity truncation / q-C*-completion / q→1 colimit remain deferred_interfaces.")


if __name__ == "__main__":
    main()
