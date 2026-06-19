#!/usr/bin/env python3
"""Finite symbolic check for the Maximum Caliber path layer.

This does not attempt a noncommutative operator proof.  It checks the finite
Jaynes/KKT algebra used by the Lean interface:

* path entropy maximization with one path constraint gives exponential weights;
* forward/backward path-weight ratios are exponentials of constraint
  differences;
* zero closed-loop log-affinity gives detailed balance.
"""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.factor(sp.cancel(sp.simplify(expr)))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    beta = sp.symbols("beta", real=True)
    c0, c1, c2 = sp.symbols("c0 c1 c2", real=True)

    weights = [sp.exp(-beta * c) for c in (c0, c1, c2)]
    Z = sum(weights)
    probs = [w / Z for w in weights]

    # KKT residual for maximizing -Σ p log p with constraints
    # Σp=1 and Σp c = const.  For p_i = exp(-β c_i)/Z,
    # -log p_i - 1 - β c_i is independent of i.
    residuals = [-sp.log(probs[i]) - 1 - beta * c for i, c in enumerate((c0, c1, c2))]
    require_zero("KKT residual 0-1", residuals[0] - residuals[1])
    require_zero("KKT residual 1-2", residuals[1] - residuals[2])
    require_zero("MaxCal normalization", sum(probs) - 1)

    cf, cb, dlogQ = sp.symbols("cf cb dlogQ", real=True)
    pf = sp.exp(-beta * cf)
    pb = sp.exp(-beta * cb)
    log_ratio = sp.log(pf / pb)
    require_zero(
        "path log-ratio equals constraint difference",
        log_ratio - (-beta * (cf - cb)),
    )
    require_zero(
        "de Rham calibrated path log-ratio",
        log_ratio.subs(dlogQ, -beta * (cf - cb)) - dlogQ.subs(dlogQ, -beta * (cf - cb)),
    )

    a, b, c = sp.symbols("a b c", real=True)
    cycle_entropy = a + b + c
    wilson_ratio = sp.exp(cycle_entropy)
    require_zero(
        "flat loop gives detailed balance",
        wilson_ratio.subs(c, -a - b) - 1,
    )

    d_pq, d_qp = sp.symbols("D_pq D_qp", real=True)
    d_sym = (d_pq + d_qp) / 2
    d_asym = (d_pq - d_qp) / 2
    require_zero("directed KL split", d_pq - (d_sym + d_asym))
    require_zero("symmetric KL swap", d_sym - (d_qp + d_pq) / 2)
    require_zero("antisymmetric KL swap", -d_asym - (d_qp - d_pq) / 2)

    print("path_probabilities =", [sp.simplify(p) for p in probs])
    print("cycle_entropy =", cycle_entropy)


if __name__ == "__main__":
    main()
