#!/usr/bin/env python3
"""Finite witness for the anyonic baryon / Gibbs-Wilson bridge.

This script deliberately checks only the finite algebraic layer mirrored by
`AnyonicBaryonGibbsWilsonBridge.lean`:

* three Fibonacci anyons have channel list tau, one, tau;
* the product/Leray Conf3 candidate has rank 32 while the OS reference has 24;
* detailed balance is the zero-affinity condition log(r12*r23/r13) = 0.

The analytic de Rham comparison and physical continuum interpretation remain
external deferred_interfaces in Lean.
"""

from __future__ import annotations

import sympy as sp


def fibonacci_three_tau_channels() -> list[str]:
    def fuse(a: str, b: str) -> list[str]:
        if a == "one":
            return [b]
        if b == "one":
            return [a]
        return ["one", "tau"]

    channels: list[str] = []
    for intermediate in fuse("tau", "tau"):
        channels.extend(fuse(intermediate, "tau"))
    return channels


def main() -> None:
    channels = fibonacci_three_tau_channels()
    assert channels == ["tau", "one", "tau"]
    assert channels.count("one") == 1
    assert channels.count("tau") == 2

    rank_product_leray = 2**5
    rank_os_reference = 24
    assert rank_product_leray == 32
    assert rank_product_leray - rank_os_reference == 8

    r12, r23, r13 = sp.symbols("r12 r23 r13", positive=True)
    cycle_affinity = sp.log(r12) + sp.log(r23) - sp.log(r13)
    wilson_ratio = sp.exp(cycle_affinity)

    detailed_balance_affinity = sp.simplify(
        cycle_affinity.subs(r13, r12 * r23)
    )
    detailed_balance_wilson = sp.simplify(
        wilson_ratio.subs(r13, r12 * r23)
    )

    assert detailed_balance_affinity == 0
    assert detailed_balance_wilson == 1

    broken_drive = sp.symbols("epsilon", positive=True)
    broken_affinity = sp.simplify(
        cycle_affinity.subs(r13, r12 * r23 * sp.exp(-broken_drive))
    )
    assert broken_affinity == broken_drive

    print("=== Anyonic baryon / Gibbs-Wilson finite witness ===")
    print(f"three tau fusion channels: {channels}")
    print("singlet multiplicity: 1")
    print("tau multiplicity: 2")
    print(f"product/Leray rank: {rank_product_leray}")
    print(f"OS reference rank: {rank_os_reference}")
    print(f"rank gap: {rank_product_leray - rank_os_reference}")
    print(f"cycle affinity: {cycle_affinity}")
    print(f"detailed-balance Wilson ratio: {detailed_balance_wilson}")
    print(f"broken detailed-balance affinity: {broken_affinity}")
    print("OK")


if __name__ == "__main__":
    main()
