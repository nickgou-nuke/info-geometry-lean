/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.LeeYangAsanoPoincareContraction

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.LeeYangAsanoPoincareContraction
open InfoGeometry.Analysis.AsanoLeeYangCircle

/-- Canonical projection capstone for Lee-Yang Asano Poincaré Contraction module. -/
theorem lee_yang_asano_poincare_contraction_canonical_capstone
    (roots : Set ℂ) (hLY : HasLeeYangProperty roots)
    (z : ℂ) (hz : z ∈ roots) (hz_ne_neg1 : z ≠ -1) (s : ℂ) (hre : s.re = 0) (hs : s ≠ 1) :
    (∀ w ∈ roots, ¬ (‖w‖ < 1)) ∧
    (∀ w ∈ roots, ¬ (1 < ‖w‖)) ∧
    ((riemannCayleyInverse z).re = 1 / 2) ∧
    (‖cayleyForward s‖ = 1) :=
  grand_lee_yang_asano_synthesis roots hLY z hz hz_ne_neg1 s hre hs

end InfoGeometry.Canonical
