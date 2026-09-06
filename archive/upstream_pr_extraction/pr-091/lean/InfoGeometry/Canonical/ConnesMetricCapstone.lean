/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Noncommutative.ConnesMetric
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Connes Geodesic Metric Capstone

Canonical umbrella export connecting the noncommutative Lipschitz geodesic metric
on the critical line ℒ_{1/2}, distance triangle inequalities, and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.ConnesMetric

open InfoGeometry.Noncommutative.ConnesMetric
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Connes Geodesic Metric & Yang-Baxter Integrability -/
theorem grand_canonical_connes_metric_synthesis (t₁ t₂ t₃ : ℝ) :
    (connesDistance t₁ t₂ = |t₁ - t₂|) ∧
    (connesDistance t₁ t₁ = 0) ∧
    (connesDistance t₁ t₂ = connesDistance t₂ t₁) ∧
    (connesDistance t₁ t₃ ≤ connesDistance t₁ t₂ + connesDistance t₂ t₃) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨connesDistance_eq_abs_sub t₁ t₂,
   connesDistance_self t₁,
   connesDistance_comm t₁ t₂,
   connesDistance_triangle t₁ t₂ t₃,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.ConnesMetric
