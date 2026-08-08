#!/usr/bin/env python3
"""SymPy witness for exceptional-point / Drazin shear collapse."""

from __future__ import annotations

import sympy as sp


def assert_true(name: str, ok: bool, detail="") -> None:
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        if detail:
            print(detail)
        raise SystemExit(1)


def main() -> int:
    x = sp.symbols("x", nonzero=True)
    N = sp.Matrix([[1, x], [0, 1]])

    lam = sp.symbols("lambda")
    charpoly = sp.factor(N.charpoly(lam).as_expr())
    assert_true("charpoly(N)=(lambda-1)^2", sp.expand(charpoly - (lam - 1) ** 2) == 0, charpoly)
    assert_true("algebraic multiplicity lambda=1 is 2", N.eigenvals().get(1) == 2, N.eigenvals())

    null = (N - sp.eye(2)).nullspace()
    assert_true("geometric multiplicity is 1", len(null) == 1, null)
    assert_true("surviving eigenline is span([1,0])", null[0] == sp.Matrix([1, 0]), null[0])

    # General eigenvector equation: x*v2 = 0, hence v2=0 for x != 0.
    v1, v2 = sp.symbols("v1 v2")
    residue = sp.simplify((N - sp.eye(2)) * sp.Matrix([v1, v2]))
    assert_true("eigenvector equation collapses to x*v2=0", residue == sp.Matrix([x * v2, 0]), residue)

    gamma, kappa = sp.symbols("gamma kappa", real=True)
    H = sp.Matrix([[sp.I * gamma, kappa], [kappa, -sp.I * gamma]])
    evals_ep = [sp.simplify(ev.subs(kappa, gamma)) for ev in H.eigenvals().keys()]
    assert_true("balanced birefringence/dichroism EP eigenvalue collapses to 0", set(evals_ep) == {0}, evals_ep)
    H_ep = H.subs(kappa, gamma)
    assert_true("EP Hamiltonian is nilpotent", sp.simplify(H_ep * H_ep) == sp.zeros(2), H_ep * H_ep)

    print("OK exceptional-point collapse witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
