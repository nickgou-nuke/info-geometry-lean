/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ParaKahlerGeneralizedMetric
import InfoGeometry.Geometry.SymplecticMetricCompatibility

/-!
# The common symplectic form of the existing phase-space metrics

On the existing carrier `E × Module.Dual ℝ E`, the complex endomorphism in
the convention `G(X,Y) = ω(X,I Y)` is `-phase G`. The para involution and
this complex endomorphism contract the same `neutralOmega` to the existing
neutral and generalized metrics. Their ordered comparison is precisely the
existing zero-B-field polarization.

`MetricDatum` supplies a symmetric duality equivalence. Positivity remains the
explicit premise of the imported `generalizedMetricForm_pos`; these identities
do not add a positivity field or a new metric/operator construction.
-/

namespace InfoGeometry.Clifford.PhaseSpaceSymplecticMetricCompatibility

open NeutralPhaseSpaceCore PhaseSpaceGeneralizedMetric ParaKahlerGeneralizedMetric
open PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open InfoGeometry.Geometry.SymplecticMetricCompatibility

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The left para contraction is the existing neutral evaluation metric. -/
theorem neutralOmega_compLeft_para :
    (neutralOmega (E := E)).compLeft neutralParaInvolution = canonicalNeutralBilin := by
  apply LinearMap.ext
  intro X
  apply LinearMap.ext
  intro Y
  simp [LinearMap.BilinForm.compLeft_apply, sub_eq_add_neg, add_comm]

/-- The right contraction has the opposite complex sign from `phase`. -/
theorem neutralOmega_compRight_neg_phase (G : MetricDatum E) :
    (neutralOmega (E := E)).compRight (-phase G) =
      (ofMetric G).generalizedMetricForm := by
  apply LinearMap.ext
  rintro ⟨x, ξ⟩
  apply LinearMap.ext
  rintro ⟨y, η⟩
  change neutralOmega (x, ξ) ((-phase G) (y, η)) =
    (ofMetric G).generalizedMetricForm (x, ξ) (y, η)
  rw [generalizedMetricForm_ofMetric_apply]
  simp [phase_apply, G.symmetric y x]

/-- The existing para involution reverses the common symplectic form. -/
theorem neutralOmega_para_antisymplectic (X Y : PhaseSpaceCarrier E) :
    neutralOmega (neutralParaInvolution X) (neutralParaInvolution Y) =
      -neutralOmega X Y := by
  rw [neutralOmega_apply, neutralOmega_apply]
  change (-Y.2 X.1) - (-X.2 Y.1) = -(Y.2 X.1 - X.2 Y.1)
  rw [_root_.neg_sub_neg, _root_.neg_sub]

/-- The positive-sign complex endomorphism preserves the common symplectic form. -/
theorem neg_phase_symplectic (G : MetricDatum E) (X Y : PhaseSpaceCarrier E) :
    neutralOmega ((-phase G) X) ((-phase G) Y) = neutralOmega X Y := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  have hx : G.gFlat x (G.gFlat.symm η) = η x := by
    rw [G.symmetric]
    simp
  have hy : G.gFlat y (G.gFlat.symm ξ) = ξ y := by
    rw [G.symmetric]
    simp
  simp [phase_apply, hx, hy, sub_eq_add_neg, add_comm]

/-- The ordered complex-para product is the already constructed polarization. -/
theorem neg_phase_mul_para (G : MetricDatum E) :
    (-phase G) * neutralParaInvolution = (ofMetric G).polarization := by
  rw [_root_.neg_mul, phase, para_polarization_anticommute,
    _root_.neg_mul, _root_.neg_neg]
  rw [_root_.mul_assoc, neutralParaInvolution_sq, _root_.mul_one]

/-- Reversing the order negates the same polarization. -/
theorem para_mul_neg_phase (G : MetricDatum E) :
    neutralParaInvolution * (-phase G) = -(ofMetric G).polarization := by
  rw [_root_.mul_neg, phase, ← _root_.mul_assoc,
    neutralParaInvolution_sq, _root_.one_mul]

section Nondegenerate

variable [Module.Projective ℝ E]

/-- The general compatibility criterion applies to the existing generalized metric. -/
theorem generalizedMetric_para_isometry (G : MetricDatum E)
    (X Y : PhaseSpaceCarrier E) :
    (ofMetric G).generalizedMetricForm (neutralParaInvolution X) (neutralParaInvolution Y) =
      (ofMetric G).generalizedMetricForm X Y := by
  have ha : (-phase G) * neutralParaInvolution =
      -(neutralParaInvolution * (-phase G)) := by
    rw [neg_phase_mul_para, para_mul_neg_phase, _root_.neg_neg]
  have h := (isometry_iff_anticommute (neutralOmega (E := E))
    neutralOmega_nondegenerate.2 (-phase G) neutralParaInvolution
    neutralParaInvolution_sq neutralOmega_para_antisymplectic).mpr ha
  rw [neutralOmega_compRight_neg_phase] at h
  exact h X Y

/-- The polarization is the unique comparison of the two existing metrics. -/
theorem neutral_to_generalized_intertwiner_iff (G : MetricDatum E)
    (T : Module.End ℝ (PhaseSpaceCarrier E)) :
    (canonicalNeutralBilin (E := E)).compLeft T = (ofMetric G).generalizedMetricForm ↔
      T = (ofMetric G).polarization := by
  have hI : (-phase G) * (-phase G) = -1 := by
    rw [_root_.neg_mul_neg, phase_sq]
  have h := metric_intertwiner_unique (neutralOmega (E := E))
    neutralOmega_nondegenerate hI neutralParaInvolution_sq (neg_phase_symplectic G) T
  rw [neutralOmega_compLeft_para, neutralOmega_compRight_neg_phase,
    para_mul_neg_phase, _root_.neg_neg] at h
  exact h

end Nondegenerate

end InfoGeometry.Clifford.PhaseSpaceSymplecticMetricCompatibility
