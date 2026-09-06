/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.LeeYangAsanoPoincareContraction

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.LeeYangAsanoPoincareContraction
open InfoGeometry.Analysis.AsanoLeeYangCircle

theorem lee_yang_asano_poincare_contraction_canonical_capstone
    (roots : Set ℂ) (hLY : HasLeeYangProperty roots)
    (z : ℂ) (hz : z ∈ roots) (hz_ne_neg1 : z ≠ -1)
    (s : ℂ) (hre : s.re = 0) (hs : s ≠ 1) :
    (∀ w ∈ roots, ¬ (‖w‖ < 1)) ∧
    (∀ w ∈ roots, ¬ (1 < ‖w‖)) ∧
    ((riemannCayleyInverse z).re = 1 / 2) ∧
    (‖cayleyForward s‖ = 1) := by
  refine ⟨inner_ball_zero_free roots hLY,
    outer_ball_zero_free roots hLY,
    riemann_inverse_on_unit_circle z (hLY hz) hz_ne_neg1,
    cayley_forward_on_imaginary_axis s hre hs⟩

end InfoGeometry.Canonical
