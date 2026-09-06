/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.SelbergApollonianGeodesicTrace

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.SelbergApollonianGeodesicTrace

/-- Canonical projection capstone for Selberg Apollonian Geodesic Trace module. -/
theorem selberg_apollonian_geodesic_trace_canonical_capstone
    (p q γ : ℝ) (k : ℕ)
    (hp : 2 ≤ p) (hq : 0 < q) (hk : 1 ≤ k) :
    (0 < primitiveGeodesicLength p) ∧
    (primitiveGeodesicLength (p * q) = primitiveGeodesicLength p + primitiveGeodesicLength q) ∧
    (0 < selbergOrbitalWeight p k) ∧
    (|spectralResonance γ p| ≤ 1) :=
  grand_selberg_trace_synthesis p q γ k hp hq hk

end InfoGeometry.Canonical
