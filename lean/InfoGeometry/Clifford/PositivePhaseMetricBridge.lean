/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ParaKahlerGeneralizedMetric
import InfoGeometry.Geometry.SymplecticComplexParaCompatibility

/-!
# The positive real phase convention on the existing cotangent carrier

The existing `phase = K * S` has the opposite orientation from the convention
`gComplex u v = omega u (I v)`. Here `I = -phase` acts on the actual carrier
`E × Module.Dual ℝ E` by `(-gSharp p, gFlat x)`. The metric datum supplies a
symmetric invertible real duality. Positivity is required separately and is
reused from the existing generalized-metric theorem.

This is a pointwise algebraic construction. No Hessian integrability, affine
connection, curvature, probability model, or entropy dynamics is assumed to
follow from the operator square identities.
-/

noncomputable section

namespace InfoGeometry.Clifford.PositivePhaseMetricBridge

open NeutralPhaseSpaceCore PhaseSpaceGeneralizedMetric
open PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open ParaKahlerGeneralizedMetric
open InfoGeometry.Geometry.SymplecticComplexParaCompatibility

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The orientation for a positive right-slot contraction by the complex map. -/
def positiveComplex (G : MetricDatum E) : Module.End ℝ (PhaseSpaceCarrier E) :=
  -(phase G)

@[simp] theorem positiveComplex_apply (G : MetricDatum E) (X : PhaseSpaceCarrier E) :
    positiveComplex G X = (-G.gFlat.symm X.2, G.gFlat X.1) := by
  simp [positiveComplex, phase_apply]

theorem positiveComplex_sq (G : MetricDatum E) :
    positiveComplex G * positiveComplex G = -1 := by
  simp only [positiveComplex, neg_mul_neg, phase_sq]

theorem positiveComplex_anticommutes_para (G : MetricDatum E) :
    positiveComplex G * neutralParaInvolution =
      -(neutralParaInvolution * positiveComplex G) := by
  apply LinearMap.ext
  intro X
  apply Prod.ext <;> simp

/-- The ordered product is the already constructed real metric polarization. -/
theorem positiveComplex_mul_para (G : MetricDatum E) :
    positiveComplex G * neutralParaInvolution = (ofMetric G).polarization := by
  rw [ofMetric_polarization]
  apply LinearMap.ext
  intro X
  apply Prod.ext <;> simp [basePolarization_apply, ofMetric]

/-- The canonical skew form and grading recover the existing neutral form. -/
theorem omega_para_metric :
    (neutralOmega (E := E)).compLeft neutralParaInvolution = canonicalNeutralBilin := by
  ext X Y
  change neutralOmega (neutralParaInvolution X) Y = canonicalNeutralBilin X Y
  simp [neutralOmega_apply, canonicalNeutralBilin_apply, add_comm]

theorem positiveComplex_preserves_omega (G : MetricDatum E) (X Y : PhaseSpaceCarrier E) :
    neutralOmega (positiveComplex G X) (positiveComplex G Y) = neutralOmega X Y := by
  simp only [positiveComplex_apply, neutralOmega_apply, map_neg]
  rw [G.symmetric Y.1 (G.gFlat.symm X.2),
    G.symmetric X.1 (G.gFlat.symm Y.2)]
  simpa only [LinearEquiv.apply_symm_apply] using
    (neg_sub_neg (X.2 Y.1) (Y.2 X.1))

/-- Exact equality of native bilinear forms fixes the left/right sign convention. -/
theorem omega_positiveComplex_metric (G : MetricDatum E) :
    (neutralOmega (E := E)).compRight (positiveComplex G) =
      (ofMetric G).generalizedMetricForm := by
  ext X Y
  change neutralOmega X (positiveComplex G Y) = (ofMetric G).generalizedMetricForm X Y
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  rw [positiveComplex_apply, neutralOmega_apply, generalizedMetricForm_ofMetric_apply]
  simp only [map_neg, sub_neg_eq_add]
  rw [G.symmetric y x]

/-- The positive order is `I * K`; the abstract bridge now has an actual consumer. -/
theorem neutral_metric_intertwining (G : MetricDatum E) :
    (canonicalNeutralBilin (E := E)).compLeft
        (positiveComplex G * neutralParaInvolution) =
      (ofMetric G).generalizedMetricForm := by
  rw [← omega_para_metric]
  rw [metric_intertwining neutralOmega (positiveComplex G) neutralParaInvolution
    (positiveComplex_sq G) neutralParaInvolution_sq
    (positiveComplex_preserves_omega G) (positiveComplex_anticommutes_para G)]
  exact omega_positiveComplex_metric G

/-- Reversing the real operators reverses the metric sign. -/
theorem neutral_metric_reverse_intertwining (G : MetricDatum E) :
    (canonicalNeutralBilin (E := E)).compLeft
        (neutralParaInvolution * positiveComplex G) =
      -(ofMetric G).generalizedMetricForm := by
  rw [← omega_para_metric]
  rw [reverse_metric_intertwining neutralOmega (positiveComplex G) neutralParaInvolution
    (positiveComplex_sq G) neutralParaInvolution_sq (positiveComplex_preserves_omega G)]
  rw [omega_positiveComplex_metric]

/-- Positivity is inherited from the specified positive base duality. -/
theorem omega_positiveComplex_pos (G : MetricDatum E)
    (hG : ∀ x, x ≠ 0 → 0 < G.gFlat x x)
    (X : PhaseSpaceCarrier E) (hX : X ≠ 0) :
    0 < neutralOmega X (positiveComplex G X) := by
  change 0 < ((neutralOmega (E := E)).compRight (positiveComplex G)) X X
  rw [omega_positiveComplex_metric]
  exact generalizedMetricForm_pos G hG X hX

end InfoGeometry.Clifford.PositivePhaseMetricBridge
