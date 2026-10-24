/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric

/-!
# Para-complex and positive generalized-metric compatibility

On the existing primal/dual carrier, the zero-B-field polarization S
anticommutes with K. The operator J = K S is complex and S reflects J to -J.
The generalized metric H = B(-, S-) is positive when the base metric is
positive. With the para-Grassmannian convention g = -B, its fundamental
symmetry is -S, not S. These are algebraic operators, not geometric holonomy.
-/

noncomputable section

namespace InfoGeometry.Clifford.ParaKahlerGeneralizedMetric

open NeutralPhaseSpaceCore PhaseSpaceGeneralizedMetric
open PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The complex phase operator attached to the chosen duality and polarization. -/
def phase (G : MetricDatum E) : Module.End ℝ (PhaseSpaceCarrier E) :=
  neutralParaInvolution * (ofMetric G).polarization

@[simp] theorem phase_apply (G : MetricDatum E) (X : PhaseSpaceCarrier E) :
    phase G X = (G.gFlat.symm X.2, -G.gFlat X.1) := by
  change neutralParaInvolution ((ofMetric G).polarization X) = _
  rw [ofMetric_polarization]
  rfl

theorem para_polarization_anticommute (G : MetricDatum E) :
    neutralParaInvolution * (ofMetric G).polarization =
      -((ofMetric G).polarization * neutralParaInvolution) := by
  ext X <;> simp [ofMetric]

theorem phase_sq (G : MetricDatum E) : phase G * phase G = -1 := by
  ext X <;> simp [phase_apply]

/-- The reflected twin is the opposite complex structure on the same carrier. -/
theorem polarization_phase_polarization (G : MetricDatum E) :
    (ofMetric G).polarization * phase G * (ofMetric G).polarization =
      -phase G := by
  ext X <;> simp [ofMetric]

/-- The sign required by the existing para-Grassmannian metric g = -B. -/
theorem negative_metric_negative_polarization (G : MetricDatum E)
    (X Y : PhaseSpaceCarrier E) :
    (-canonicalNeutralBilin (E := E)) X (-(ofMetric G).polarization Y) =
      (ofMetric G).generalizedMetricForm X Y := by
  simp [generalizedMetricForm_apply, add_comm]

theorem generalizedMetricForm_self (G : MetricDatum E) (X : PhaseSpaceCarrier E) :
    (ofMetric G).generalizedMetricForm X X =
      G.gFlat X.1 X.1 + G.gFlat (G.gFlat.symm X.2) (G.gFlat.symm X.2) := by
  rw [generalizedMetricForm_ofMetric_apply]
  simp

theorem generalizedMetricForm_nonneg (G : MetricDatum E)
    (hG : ∀ x, 0 ≤ G.gFlat x x) (X : PhaseSpaceCarrier E) :
    0 ≤ (ofMetric G).generalizedMetricForm X X := by
  rw [generalizedMetricForm_self]
  exact add_nonneg (hG _) (hG _)

theorem generalizedMetricForm_pos (G : MetricDatum E)
    (hG : ∀ x, x ≠ 0 → 0 < G.gFlat x x)
    (X : PhaseSpaceCarrier E) (hX : X ≠ 0) :
    0 < (ofMetric G).generalizedMetricForm X X := by
  have hn (x : E) : 0 ≤ G.gFlat x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hG x hx).le
  rw [generalizedMetricForm_self]
  by_cases hx : X.1 = 0
  · have hξ : G.gFlat.symm X.2 ≠ 0 := by
      intro h
      have : X.2 = 0 := by
        have := congrArg G.gFlat h
        simpa using this
      exact hX (Prod.ext hx this)
    exact add_pos_of_nonneg_of_pos (hn _) (hG _ hξ)
  · exact add_pos_of_pos_of_nonneg (hG _ hx) (hn _)

/-- Positive definiteness gives actual nondegeneracy without a finite-rank assumption. -/
theorem generalizedMetricForm_nondegenerate (G : MetricDatum E)
    (hG : ∀ x, x ≠ 0 → 0 < G.gFlat x x) :
    (ofMetric G).generalizedMetricForm.Nondegenerate := by
  constructor
  · intro X hX
    by_contra hn
    have hp := generalizedMetricForm_pos G hG X hn
    rw [hX X] at hp
    exact (lt_irrefl 0) hp
  · intro X hX
    by_contra hn
    have hp := generalizedMetricForm_pos G hG X hn
    rw [hX X] at hp
    exact (lt_irrefl 0) hp

end InfoGeometry.Clifford.ParaKahlerGeneralizedMetric
