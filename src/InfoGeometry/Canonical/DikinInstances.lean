/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.UnifiedDikinGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity

/-!
# Dikin Instances — Lineage Integration (Part 1: Canonical Souriau Metric Instance on `ℝ`)

This file maps the Souriau scale-space Dikin metric construction into the
`DikinMetric` framework defined in `UnifiedDikinGeometry.lean`:
- `Quantum.DikinSouriauTrap`: `g_ξ(v) = (2 / cosh² ξ) · v²` on `ℝ`.

No `sorry`, `admit`, or axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
-/

noncomputable section

/-- The Souriau Dikin metric on `ℝ`: `g_ξ(v) = (2 / cosh² ξ) · v²`. -/
def souriauDikinMetric (ξ v : ℝ) : ℝ :=
  (2 / Real.cosh ξ ^ 2) * v ^ 2

instance instDikinMetricReal : DikinMetric ℝ where
  dikin_metric := souriauDikinMetric
  dikin_ellipsoid := fun ξ r => {y : ℝ | souriauDikinMetric ξ (y - ξ) ≤ r ^ 2}
  dikin_metric_zero := fun ξ => by
    simp [souriauDikinMetric]
  dikin_metric_pos := fun {ξ v} hv => by
    have h₁ : 0 < Real.cosh ξ := Real.cosh_pos ξ
    have h₂ : 0 < Real.cosh ξ ^ 2 := sq_pos_of_pos h₁
    have h₃ : 0 < 2 / Real.cosh ξ ^ 2 := div_pos zero_lt_two h₂
    have h₅ : 0 < v ^ 2 := sq_pos_of_ne_zero hv
    exact mul_pos h₃ h₅
  dikin_ellipsoid_def := fun _ _ => rfl

end
