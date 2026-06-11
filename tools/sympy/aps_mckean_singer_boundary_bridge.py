#!/usr/bin/env python3
"""Finite APS / McKean-Singer boundary bridge witness.

Mirrors `InfoGeometry.Canonical.APSMcKeanSingerBoundaryBridge`.

The checked statement is only scalar plumbing:

    finite_supertrace = analytic_index
    analytic_index = bulk_ahat_term - eta_correction
    bulk_ahat_term = 0
    eta_correction = 0
    -----------------------------------------------
    finite_supertrace = analytic_index = 0

No heat-kernel theorem, APS theorem, Seiberg-Witten theorem, KMS geometry, or
Riemann-zeta consequence is asserted here.
"""

import sympy as sp


def main():
    bulk_ahat_term = sp.Integer(0)
    eta_correction = sp.Integer(0)
    analytic_index = sp.simplify(bulk_ahat_term - eta_correction)
    finite_supertrace = analytic_index

    assert analytic_index == 0
    assert finite_supertrace == 0

    print("APS / McKean-Singer scalar bridge:")
    print(f"  analytic_index = bulk_ahat_term - eta_correction = {analytic_index}")
    print(f"  finite_supertrace = analytic_index = {finite_supertrace}")
    print("  verified: both vanish under explicit Ahat and eta vanishing premises")


if __name__ == "__main__":
    main()
