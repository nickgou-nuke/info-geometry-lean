/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Differential.PoincareFisherRao
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.PoincareFisherRao

open Matrix
open InfoGeometry.Differential.PoincareFisherRao
open InfoGeometry.Canonical.YangBaxterProof

/-- Canonical synthesis of the finite Poincaré Fisher--Rao metric packet and
    the independent Yang--Baxter involution identities. -/
theorem grand_canonical_poincare_fisher_rao_synthesis
    (p : UpperHalfPlanePoint) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (vx vy : ℝ) (lam_scale : ℝ) (h_lam : 0 < lam_scale) (c : ℝ) :
    (fisherMetricMatrix p 0 0 = 1 / p.y ^ 2) ∧
    (fisherMetricMatrix p 0 1 = 0) ∧
    ((fisherMetricMatrix p).det = 1 / p.y ^ 4) ∧
    (Real.log (fisherMetricMatrix p).det = -4 * Real.log p.y) ∧
    (0 < dotProduct (mulVec (fisherMetricMatrix p) v) v) ∧
    (fisherMetricMatrix ⟨p.x + c, p.y, p.y_pos⟩ = fisherMetricMatrix p) ∧
    (fisherLineElement ⟨lam_scale * p.x, lam_scale * p.y,
      mul_pos h_lam p.y_pos⟩ (lam_scale * vx) (lam_scale * vy) =
      fisherLineElement p vx vy) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) := by
  exact ⟨rfl, rfl, fisher_metric_det p, fisher_metric_log_det p,
    fisher_metric_pos_def p v hv,
    fisher_metric_horizontal_translation_invariant p c,
    fisher_line_element_scaling p vx vy lam_scale h_lam,
    F_sq, F_B_F_eq_R⟩

end InfoGeometry.Canonical.PoincareFisherRao
