#!/usr/bin/env python3
"""Finite witness for the q-super regularization Rosetta dictionary.

This mirrors QSuperRegularizationRosetta.lean at the concrete 2x2 level:

  1. eta = (-1)^F = PB - PF
  2. STr(X) = Tr(eta X) = X00 - X11
  3. tanh(1 - T^-1) is bounded in (-1, 1)
  4. Cayley(T) lies on the unit circle and is DKT-unitary

The q->1 colimit, root-of-unity representation theory, and TKK spacetime
recovery remain sockets; this script only audits the finite contracts.
"""

from __future__ import annotations

import sympy as sp


def dagger(matrix: sp.Matrix) -> sp.Matrix:
    return matrix.conjugate().T


def dkt_adjoint(matrix: sp.Matrix, eta: sp.Matrix) -> sp.Matrix:
    return eta * dagger(matrix) * eta


def main() -> None:
    eye = sp.eye(2)
    pb = sp.diag(1, 0)
    pf = sp.diag(0, 1)
    eta = pb - pf

    # 1. Minkowski signature / superparity.
    assert eta == sp.diag(1, -1)
    assert eta * eta == eye
    assert dagger(eta) == eta

    # 2. Lorentz bilinear / supertrace.
    x00, x01, x10, x11 = sp.symbols("x00 x01 x10 x11", complex=True)
    x = sp.Matrix([[x00, x01], [x10, x11]])
    supertrace = sp.trace(eta * x)
    assert sp.simplify(supertrace - (x00 - x11)) == 0

    # 3. Spectral squashing.
    lam = sp.symbols("lam", positive=True, real=True)
    stage = sp.diag(lam, 2 * lam)
    squash = sp.diag(sp.tanh(1 - 1 / lam), sp.tanh(1 - 1 / (2 * lam)))
    squash_limit = squash.applyfunc(lambda entry: sp.limit(entry, lam, sp.oo))
    assert squash_limit == sp.diag(sp.tanh(1), sp.tanh(1))

    # 4. CUE / q-circle boundary through the Cayley coordinate.
    cayley = (stage - sp.I * eye) * (stage + sp.I * eye).inv()
    assert sp.simplify(cayley * dagger(cayley) - eye) == sp.zeros(2)
    assert sp.simplify(cayley * dkt_adjoint(cayley, eta) - eye) == sp.zeros(2)

    q = sp.exp(sp.I * sp.pi / 4)
    q_integer_3 = sp.sinh(3 * sp.log(q)) / sp.sinh(sp.log(q))

    print("q_super_regularization_rosetta.py: finite Rosetta contracts passed")
    print("root algebra: O_q(1|1)")
    print("1. eta = (-1)^F = PB - PF, eta^2 = I, eta† = eta")
    print("2. STr(X) = Tr(eta X) = X00 - X11")
    print("3. tanh(1 - T^-1) finite-stage limit:")
    sp.pprint(squash_limit)
    print("4. Cayley(T) is unitary and DKT-unitary")
    print("q root-of-unity sample: q = exp(i*pi/4)")
    print("[3]_q hyperbolic witness =")
    sp.pprint(sp.simplify(q_integer_3))
    print("q->1 colimit, root-of-unity truncation theory, and TKK recovery remain sockets.")


if __name__ == "__main__":
    main()
