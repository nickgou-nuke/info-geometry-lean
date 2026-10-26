/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.BornRuleCore
import InfoGeometry.Physics.NuclearEffectiveObservables

/-!
# Real rectangular Krein transport of effective observables

The initial and final model and ambient carriers may all differ. Their real
fundamental symmetries determine the rectangular Krein adjoint. The indefinite
matrix element is transported by `Omega_f^sharp O Omega_i`; inserting the final
fundamental symmetry instead recovers the positive real readout already owned
by `NuclearEffectiveObservables` and `BornRuleCore`.

The induced positive norm remains the existing Gram operator. Injectivity
gives strict positivity of that norm, not of the raw indefinite pullback.
An arbitrary supplied transition operator is not asserted to have strength at
most one or to be a physical electromagnetic multipole.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearRealKreinObservables

open ContinuousLinearMap
open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open InfoGeometry.Krein.BornRuleCore
open InfoGeometry.Physics.NuclearEffectiveObservables

section RectangularAdjoint

variable {X Y Z : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [KreinSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [KreinSpace Y]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [KreinSpace Z]

/-- The domain and codomain fundamental symmetries remain independent. -/
def rectangularKreinAdjoint (A : X →L[ℝ] Y) : Y →L[ℝ] X :=
  (jCLM (H := X)).comp (A.adjoint.comp (jCLM (H := Y)))

theorem rectangularKreinAdjoint_eq_owner (A : X →L[ℝ] X) :
    rectangularKreinAdjoint A = kreinAdjoint A := rfl

theorem kreinInner_rectangularKreinAdjoint (A : X →L[ℝ] Y) (x : X) (y : Y) :
    kreinInner (A x) y = kreinInner x (rectangularKreinAdjoint A y) := by
  change inner ℝ (KreinSpace.J (A x)) y =
    inner ℝ (KreinSpace.J x)
      (KreinSpace.J (A.adjoint (KreinSpace.J y)))
  rw [KreinSpace.J_selfAdj]
  rw [← A.adjoint_inner_right x (KreinSpace.J y)]
  exact ((KreinSpace.J : X ≃ₗᵢ[ℝ] X).inner_map_map
    x (A.adjoint (KreinSpace.J y))).symm

theorem rectangularKreinAdjoint_comp (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z) :
    rectangularKreinAdjoint (B.comp A) =
      (rectangularKreinAdjoint A).comp (rectangularKreinAdjoint B) := by
  simp [rectangularKreinAdjoint, adjoint_comp, comp_assoc]

theorem rectangularKreinAdjoint_involutive (A : X →L[ℝ] Y) :
    rectangularKreinAdjoint (rectangularKreinAdjoint A) = A := by
  simp [rectangularKreinAdjoint, adjoint_comp, comp_assoc]

/-- Intertwining the two symmetries is an explicit sufficient condition for
the rectangular Krein and positive adjoints to agree. -/
theorem rectangularKreinAdjoint_eq_adjoint_of_intertwines (A : X →L[ℝ] Y)
    (hA : (jCLM (H := Y)).comp A = A.comp (jCLM (H := X))) :
    rectangularKreinAdjoint A = A.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint hA
  have h' : A.adjoint.comp (jCLM (H := Y)) =
      (jCLM (H := X)).comp A.adjoint := by
    simpa only [adjoint_comp, adjoint_jCLM] using h
  unfold rectangularKreinAdjoint
  rw [h']
  exact jCLM_comp_jCLM_comp A.adjoint

theorem kreinInner_rectangular_pullback (A : X →L[ℝ] Y) (x y : X) :
    kreinInner x (rectangularKreinAdjoint A (A y)) =
      kreinInner (A x) (A y) :=
  (kreinInner_rectangularKreinAdjoint A x (A y)).symm

end RectangularAdjoint

section EffectiveTransport

variable {Mi Mf Hi Hf : Type*}
variable [NormedAddCommGroup Mi] [InnerProductSpace ℝ Mi] [CompleteSpace Mi]
  [KreinSpace Mi]
variable [NormedAddCommGroup Mf] [InnerProductSpace ℝ Mf] [CompleteSpace Mf]
  [KreinSpace Mf]
variable [NormedAddCommGroup Hi] [InnerProductSpace ℝ Hi] [CompleteSpace Hi]
  [KreinSpace Hi]
variable [NormedAddCommGroup Hf] [InnerProductSpace ℝ Hf] [CompleteSpace Hf]
  [KreinSpace Hf]

/-- Indefinite transport, expressed through the existing effective operator. -/
def kreinEffectiveOperator (Ωi : Mi →L[ℝ] Hi) (Ωf : Mf →L[ℝ] Hf)
    (O : Hi →L[ℝ] Hf) : Mi →L[ℝ] Mf :=
  (jCLM (H := Mf)).comp
    (effectiveOperator Ωi Ωf ((jCLM (H := Hf)).comp O))

theorem kreinEffectiveOperator_eq_sharp (Ωi : Mi →L[ℝ] Hi)
    (Ωf : Mf →L[ℝ] Hf) (O : Hi →L[ℝ] Hf) :
    kreinEffectiveOperator Ωi Ωf O =
      (rectangularKreinAdjoint Ωf).comp (O.comp Ωi) := by
  simp only [kreinEffectiveOperator, rectangularKreinAdjoint,
    effectiveOperator, comp_assoc]

theorem kreinInner_effective_transport (Ωi : Mi →L[ℝ] Hi)
    (Ωf : Mf →L[ℝ] Hf) (O : Hi →L[ℝ] Hf) (xi : Mi) (xf : Mf) :
    kreinInner xf (kreinEffectiveOperator Ωi Ωf O xi) =
      kreinInner (Ωf xf) (O (Ωi xi)) := by
  rw [kreinEffectiveOperator_eq_sharp]
  exact (kreinInner_rectangularKreinAdjoint Ωf xf (O (Ωi xi))).symm

/-- An inserted ambient symmetry converts the indefinite transport into the
model symmetry followed by the existing positive effective operator. -/
theorem kreinEffectiveOperator_fundamentalSymmetry (Ωi : Mi →L[ℝ] Hi)
    (Ωf : Mf →L[ℝ] Hf) (O : Hi →L[ℝ] Hf) :
    kreinEffectiveOperator Ωi Ωf ((jCLM (H := Hf)).comp O) =
      (jCLM (H := Mf)).comp (effectiveOperator Ωi Ωf O) := by
  unfold kreinEffectiveOperator
  rw [jCLM_comp_jCLM_comp]

theorem positive_krein_effective_amplitude (Ωi : Mi →L[ℝ] Hi)
    (Ωf : Mf →L[ℝ] Hf) (O : Hi →L[ℝ] Hf) (xi : Mi) (xf : Mf) :
    kreinInner xf
        (kreinEffectiveOperator Ωi Ωf ((jCLM (H := Hf)).comp O) xi) =
      inner ℝ xf (effectiveOperator Ωi Ωf O xi) := by
  rw [kreinEffectiveOperator_fundamentalSymmetry]
  exact kreinInner_fundamentalSymmetry_right xf (effectiveOperator Ωi Ωf O xi)

theorem positive_krein_effective_transport (Ωi : Mi →L[ℝ] Hi)
    (Ωf : Mf →L[ℝ] Hf) (O : Hi →L[ℝ] Hf) (xi : Mi) (xf : Mf) :
    kreinInner xf
        (kreinEffectiveOperator Ωi Ωf ((jCLM (H := Hf)).comp O) xi) =
      kreinAdaptedAmplitude (Ωf xf) (O (Ωi xi)) := by
  rw [positive_krein_effective_amplitude, kreinAdaptedAmplitude_eq_inner]
  exact inner_effectiveOperator Ωi Ωf O xi xf

/-- The positive pullback is the already-owned Gram weight. -/
theorem positive_krein_normMetric (Ω : Mi →L[ℝ] Hi) (x : Mi) :
    kreinInner x ((jCLM (H := Mi)) (normMetric Ω x)) = metricWeight Ω x := by
  change kreinInner x ((KreinSpace.J : Mi ≃ₗᵢ[ℝ] Mi) (normMetric Ω x)) =
    metricWeight Ω x
  rw [kreinInner_fundamentalSymmetry_right, inner_normMetric,
    real_inner_self_eq_norm_sq, metricWeight_eq_norm_sq]

theorem positive_krein_pullback_weight (Ω : Mi →L[ℝ] Hi) (x : Mi) :
    kreinInner x
        (rectangularKreinAdjoint Ω ((jCLM (H := Hi)) (Ω x))) =
      metricWeight Ω x := by
  rw [← kreinInner_rectangularKreinAdjoint]
  change kreinInner (Ω x) ((KreinSpace.J : Hi ≃ₗᵢ[ℝ] Hi) (Ω x)) =
    metricWeight Ω x
  rw [kreinInner_fundamentalSymmetry_right,
    real_inner_self_eq_norm_sq, metricWeight_eq_norm_sq]

theorem positive_krein_normMetric_nonneg (Ω : Mi →L[ℝ] Hi) (x : Mi) :
    0 ≤ kreinInner x ((jCLM (H := Mi)) (normMetric Ω x)) := by
  rw [positive_krein_normMetric]
  exact metricWeight_nonneg Ω x

theorem positive_krein_normMetric_pos (Ω : Mi →L[ℝ] Hi)
    (hΩ : Function.Injective Ω) {x : Mi} (hx : x ≠ 0) :
    0 < kreinInner x ((jCLM (H := Mi)) (normMetric Ω x)) := by
  rw [positive_krein_normMetric]
  exact metricWeight_pos Ω hΩ hx

/-- Normalization uses the two positive induced norms. The algebraic identity
also follows the existing totalized convention when a reconstructed state is
zero; strict positivity is supplied separately by the preceding theorem. -/
theorem normalized_positive_krein_transition_strength (Ωi : Mi →L[ℝ] Hi)
    (Ωf : Mf →L[ℝ] Hf) (O : Hi →L[ℝ] Hf) (xi : Mi) (xf : Mf) :
    kreinAdaptedAmplitude (normalizedState Ωf xf)
        (O (normalizedState Ωi xi)) ^ 2 =
      (kreinInner xf
        (kreinEffectiveOperator Ωi Ωf ((jCLM (H := Hf)).comp O) xi)) ^ 2 /
        (metricWeight Ωf xf * metricWeight Ωi xi) := by
  rw [kreinAdaptedAmplitude_eq_inner, positive_krein_effective_amplitude]
  simpa only [Real.norm_eq_abs, sq_abs] using
    (normalized_transition_strength (𝕜 := ℝ) Ωi Ωf O xi xf)

end EffectiveTransport

end InfoGeometry.Physics.NuclearRealKreinObservables
