import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.Metric

/-!
# InfoGeometry.Projective.Null

Null and grading predicates on projective doubled-space rays.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Projective

open InfoGeometry.Krein

section GradeNull

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inGradePlus_smul (a : ℝ) {v : DoubledSpace E}
    (hv : inGradePlus v) :
    inGradePlus (a • v) := by
  rw [inGradePlus] at *
  simpa [hv]

lemma inGradeMinus_smul (a : ℝ) {v : DoubledSpace E}
    (hv : inGradeMinus v) :
    inGradeMinus (a • v) := by
  rw [inGradeMinus] at *
  simpa [hv]

lemma inGradePlus_smul_iff {a : ℝ} (ha : a ≠ 0) (v : DoubledSpace E) :
    inGradePlus (a • v) ↔ inGradePlus v := by
  constructor
  · intro hv
    have : inGradePlus (a⁻¹ • (a • v)) := inGradePlus_smul a⁻¹ hv
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro hv
    exact inGradePlus_smul a hv

lemma inGradeMinus_smul_iff {a : ℝ} (ha : a ≠ 0) (v : DoubledSpace E) :
    inGradeMinus (a • v) ↔ inGradeMinus v := by
  constructor
  · intro hv
    have : inGradeMinus (a⁻¹ • (a • v)) := inGradeMinus_smul a⁻¹ hv
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro hv
    exact inGradeMinus_smul a hv

/-- Grade `+` rays, well-defined on the projective quotient. -/
def IsGradePlusRay : ProjectiveState E → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => inGradePlus v)
    (by
      intro v w hvw
      rcases hvw with ⟨a, h⟩
      rw [← h]
      exact propext (inGradePlus_smul_iff (Units.ne_zero a) w))

/-- Grade `-` rays, well-defined on the projective quotient. -/
def IsGradeMinusRay : ProjectiveState E → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => inGradeMinus v)
    (by
      intro v w hvw
      rcases hvw with ⟨a, h⟩
      rw [← h]
      exact propext (inGradeMinus_smul_iff (Units.ne_zero a) w))

@[simp] lemma IsGradePlusRay_projectivize (v : DoubledSpace E) :
    IsGradePlusRay (projectivize v) ↔ inGradePlus v := Iff.rfl

@[simp] lemma IsGradeMinusRay_projectivize (v : DoubledSpace E) :
    IsGradeMinusRay (projectivize v) ↔ inGradeMinus v := Iff.rfl

/-- “Grade-null” rays: points lying in either grading eigenspace. -/
def IsGradeNullRay (q : ProjectiveState E) : Prop :=
  IsGradePlusRay q ∨ IsGradeMinusRay q

lemma IsGradePlusRay_vacuum : IsGradePlusRay (vacuum E) := by
  simp [vacuum, inGradePlus]

lemma IsGradeMinusRay_vacuum : IsGradeMinusRay (vacuum E) := by
  simp [vacuum, inGradeMinus]

lemma IsGradeNullRay_vacuum : IsGradeNullRay (vacuum E) :=
  Or.inl IsGradePlusRay_vacuum

end GradeNull

section MetricNull

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- “Metric-null” / isotropic doubled vectors for the neutral Hessian form. -/
def IsMetricNull (v : DoubledSpace E) : Prop :=
  hessian_indefinite_form v v = 0

lemma isMetricNull_smul (a : ℝ) {v : DoubledSpace E}
    (hv : IsMetricNull v) :
    IsMetricNull (a • v) := by
  have hv' : KreinSpace.kreinInner (H := DoubledSpace E) v v = 0 := by
    simpa [IsMetricNull, hessian_indefinite_form] using hv
  unfold IsMetricNull
  change KreinSpace.kreinInner (H := DoubledSpace E) (a • v) (a • v) = 0
  rw [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right]
  calc
    a * (a * KreinSpace.kreinInner (H := DoubledSpace E) v v) = a * (a * 0) := by rw [hv']
    _ = 0 := by ring

lemma isMetricNull_smul_iff {a : ℝ} (ha : a ≠ 0) (v : DoubledSpace E) :
    IsMetricNull (a • v) ↔ IsMetricNull v := by
  constructor
  · intro hv
    have : IsMetricNull (a⁻¹ • (a • v)) := isMetricNull_smul a⁻¹ hv
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro hv
    exact isMetricNull_smul a hv

/-- Metric-null rays, well-defined on the projective quotient. -/
def IsMetricNullRay : ProjectiveState E → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => IsMetricNull v)
    (by
      intro v w hvw
      rcases hvw with ⟨a, h⟩
      rw [← h]
      exact propext (isMetricNull_smul_iff (Units.ne_zero a) w))

@[simp] lemma IsMetricNullRay_projectivize (v : DoubledSpace E) :
    IsMetricNullRay (projectivize v) ↔ IsMetricNull v := Iff.rfl

lemma IsMetricNullRay_vacuum : IsMetricNullRay (vacuum E) := by
  simp [vacuum, IsMetricNull, hessian_indefinite_form]

end MetricNull

section UnifiedNull

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Unified nullness on rays: vacuum, grade-null, or metric-null. -/
def IsNullRay (q : ProjectiveState E) : Prop :=
  q = vacuum E ∨
  IsGradeNullRay q ∨
  IsMetricNullRay q

lemma IsNullRay_vacuum : IsNullRay (vacuum E) :=
  Or.inl rfl

end UnifiedNull

end InfoGeometry.Projective
