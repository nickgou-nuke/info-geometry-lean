#!/usr/bin/env python3
"""SymPy witness for the Amari / Souriau information-geometry bridge.

This script checks the symbolic identities that motivate the Lean bridge:

- d/dθ log Q = Q'/Q
- Hessian(log Q) for a concrete strictly convex potential
- Bregman divergence for a quadratic log-partition potential
- Souriau-style pairing as the shifted moment readout

It is a witness, not a proof of the full geometric theory.
"""

import sympy as sp


def main() -> None:
    theta, theta0, beta, mu = sp.symbols("theta theta0 beta mu", real=True)
    E, N = sp.symbols("E N", real=True)

    Q = sp.Function("Q")
    Psi = sp.log(Q(theta))
    dPsi = sp.diff(Psi, theta)
    expected_dPsi = sp.diff(Q(theta), theta) / Q(theta)
    assert sp.simplify(dPsi - expected_dPsi) == 0

    print("General log-potential derivative:")
    sp.pprint(sp.simplify(dPsi))

    # Concrete convex example: Q(theta) = exp(theta^2/2), Psi = theta^2/2.
    Psi_quad = theta**2 / 2
    grad_quad = sp.diff(Psi_quad, theta)
    hess_quad = sp.diff(Psi_quad, theta, 2)
    assert sp.simplify(grad_quad - theta) == 0
    assert sp.simplify(hess_quad - 1) == 0

    bregman_quad = (
        Psi_quad.subs(theta, theta)
        - Psi_quad.subs(theta, theta0)
        - sp.diff(Psi_quad, theta).subs(theta, theta0) * (theta - theta0)
    )
    assert sp.simplify(bregman_quad - (theta - theta0) ** 2 / 2) == 0

    print("\nConcrete quadratic log-partition potential:")
    print("  Psi(theta) = theta^2 / 2")
    print("  grad Psi =")
    sp.pprint(grad_quad)
    print("  Hessian Psi =")
    sp.pprint(hess_quad)
    print("  Bregman divergence =")
    sp.pprint(sp.simplify(bregman_quad))

    # Souriau-style finite pairing / shifted moment readout.
    shifted_moment = E - mu * N
    pairing = beta * shifted_moment
    density = sp.exp(-pairing)
    assert sp.simplify(pairing - beta * (E - mu * N)) == 0

    print("\nSouriau pairing / shifted moment:")
    print("  shifted moment =", shifted_moment)
    print("  pairing =", pairing)
    print("  unnormalized density =", density)

    print("\nSUCCESS: Amari/Souriau information-geometry witness passed.")


if __name__ == "__main__":
    main()
