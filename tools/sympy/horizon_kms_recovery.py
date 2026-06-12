from __future__ import annotations

import sympy as sp


def main() -> None:
    # Finite toy model mirroring the Lean theorem surface:
    # exteriorData(observedDefect(x,y)) = memoryReadout(hiddenTotal(x,y)).
    # This is only a concrete linear sanity check, not a proof of the abstract Lean theorem.
    x1, x2, y1, y2 = sp.symbols('x1 x2 y1 y2', real=True)
    x = sp.Matrix([x1, x2])
    y = sp.Matrix([y1, y2])

    # Grade ±2 pieces in a toy two-component current space J = R^2.
    gneg = sp.Matrix([x1, 0])
    gpos = sp.Matrix([0, y2])

    hidden_total = gneg + gpos

    # Observer sees the visible/hidden projection as a defect observable in Obs = R^2.
    observed_defect = hidden_total

    # Exterior reconstruction map Obs -> Memory and memory readout J -> Memory.
    exterior_data = sp.eye(2)
    memory_readout = sp.eye(2)

    lhs = sp.simplify(exterior_data * observed_defect)
    rhs = sp.simplify(memory_readout * hidden_total)

    assert lhs == rhs, f'recovery law failed: lhs={lhs}, rhs={rhs}'

    # Also assert componentwise equality explicitly for clearer failure modes.
    assert sp.simplify(lhs[0] - rhs[0]) == 0
    assert sp.simplify(lhs[1] - rhs[1]) == 0

    # Natural-unit calibration sanity check mirroring β * κ = 2π.
    kappa = sp.symbols('kappa', positive=True, real=True)
    beta = 2 * sp.pi / kappa
    assert sp.simplify(beta * kappa - 2 * sp.pi) == 0

    print('horizon_kms_recovery: finite recovery-law sanity check passed')
    print(f'lhs = {lhs}')
    print(f'rhs = {rhs}')
    print(f'beta * kappa = {sp.simplify(beta * kappa)}')


if __name__ == '__main__':
    main()
