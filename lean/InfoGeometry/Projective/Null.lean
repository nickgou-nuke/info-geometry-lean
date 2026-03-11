import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Krein.Metric

/-!
# InfoGeometry.Projective.Null

Null and grading predicates on projective doubled-space rays.
Utilizes the canonical Krein-Clifford definitions.
-/

namespace InfoGeometry.Projective

open InfoGeometry.Krein

section GradeNull

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma inGradePlus_smul (a : ℝ) {v : DoubledSpace E}
    (hv : inGradePlus v) :
    inGradePlus (a • v) := by
  rw [inGradePlus] at *
  simp [hv]

lemma inGradeMinus_smul (a : ℝ) {v : DoubledSpace E}
    (hv : inGradeMinus v) :
    inGradeMinus (a • v) := by
  rw [inGradeMinus] at *
  simp [hv]

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

lemma inGradePlus_sameRay_iff {v w : DoubledSpace E}
    (hvw : SameRayDoubled v w) :
    inGradePlus v ↔ inGradePlus w := by
  rcases hvw with ⟨a, ha, rfl⟩
  rw [inGradePlus_smul_iff ha]

lemma inGradeMinus_sameRay_iff {v w : DoubledSpace E}
    (hvw : SameRayDoubled v w) :
    inGradeMinus v ↔ inGradeMinus w := by
  rcases hvw with ⟨a, ha, rfl⟩
  rw [inGradeMinus_smul_iff ha]

/-- Grade `+` rays, well-defined on the projective quotient. -/
def IsGradePlusRay : ProjectiveState E → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => inGradePlus v)
    (by
      intro v w hvw
      exact propext (inGradePlus_sameRay_iff hvw))

/-- Grade `-` rays, well-defined on the projective quotient. -/
def IsGradeMinusRay : ProjectiveState E → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => inGradeMinus v)
    (by
      intro v w hvw
      exact propext (inGradeMinus_sameRay_iff hvw))

@[simp] lemma IsGradePlusRay_projectivize (v : DoubledSpace E) :
    IsGradePlusRay (projectivize v) ↔ inGradePlus v := Iff.rfl

@[simp] lemma IsGradeMinusRay_projectivize (v : DoubledSpace E) :
    IsGradeMinusRay (projectivize v) ↔ inGradeMinus v := Iff.rfl

/-- Coordinate form for grade `+`: `J(x,ξ)=(x,ξ)` iff `ξ=x`. -/
@[simp] lemma inGradePlus_iff_coords (x ξ : E) :
    inGradePlus (to_doubled x ξ) ↔ ξ = x := by
  rw [inGradePlus]
  constructor
  · intro h
    have h_snd : (modular_j E (to_doubled x ξ)).snd = (to_doubled x ξ).snd := congrArg DoubledSpace.snd h
    simpa using h_snd
  · intro h
    subst h
    simp [modular_j_apply]

/-- Coordinate form for grade `-`: `J(x,ξ)=-(x,ξ)` iff `ξ=-x`. -/
@[simp] lemma inGradeMinus_iff_coords (x ξ : E) :
    inGradeMinus (to_doubled x ξ) ↔ ξ = -x := by
  rw [inGradeMinus]
  constructor
  · intro h
    have h_snd : (modular_j E (to_doubled x ξ)).snd = (-(to_doubled x ξ)).snd := congrArg DoubledSpace.snd h
    simpa using h_snd
  · intro h
    subst h
    simp [modular_j_apply]

/-- “Grade-null” rays: points lying in either grading eigenspace. -/
def IsGradeNullRay (q : ProjectiveState E) : Prop :=
  IsGradePlusRay q ∨ IsGradeMinusRay q

lemma IsGradePlusRay_vacuum : IsGradePlusRay (vacuum E) := by
  simp [vacuum, inGradePlus]

lemma IsGradeMinusRay_vacuum : IsGradeMinusRay (vacuum E) := by
  simp [vacuum, inGradeMinus]

lemma IsGradeNullRay_vacuum : IsGradeNullRay (vacuum E) :=
  Or.inl IsGradePlusRay_vacuum

/-- A ray cannot be both grade `+` and grade `-` unless it is the vacuum ray. -/
lemma gradePlus_and_gradeMinus_implies_vacuum
    (q : ProjectiveState E)
    (hqPlus : IsGradePlusRay q)
    (hqMinus : IsGradeMinusRay q) :
    q = vacuum E := by
  revert hqPlus hqMinus
  refine Quotient.inductionOn q ?_
  intro v hvPlus hvMinus
  obtain ⟨x, ξ⟩ := WithLp.ofLp v
  have hv : v = to_doubled x ξ := by simp
  rw [hv] at hvPlus hvMinus
  have hξx : ξ = x := (inGradePlus_iff_coords x ξ).mp hvPlus
  have hξnegx : ξ = -x := (inGradeMinus_iff_coords x ξ).mp hvMinus
  have hxneg : x = -x := hξx.symm.trans hξnegx
  have hx0 : x = 0 := by
    apply_fun (fun t => (1/2 : ℝ) • t) at hxneg
    simpa [smul_neg, sub_eq_zero] using add_halves x
  have hξ0 : ξ = 0 := hx0 ▸ hξx
  simp [vacuum, hv, hx0, hξ0]

end GradeNull

section MetricNull

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- “Metric-null” / isotropic doubled vectors for the neutral Hessian form. -/
def IsMetricNull (v : DoubledSpace E) : Prop :=
  hessian_indefinite_form v v = 0

@[simp] lemma isMetricNull_iff_norm_sq_eq (x ξ : E) :
    IsMetricNull (to_doubled x ξ) ↔ ‖x‖ ^ 2 = ‖ξ‖ ^ 2 := by
  unfold IsMetricNull
  simp [hessian_indefinite_form, krein_inner_prod_l2, real_inner_self_eq_norm_sq, sub_eq_zero]

lemma isMetricNull_smul (a : ℝ) {v : DoubledSpace E}
    (hv : IsMetricNull v) :
    IsMetricNull (a • v) := by
  unfold IsMetricNull at *
  simp [hessian_indefinite_form, KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right, hv]

lemma isMetricNull_smul_iff {a : ℝ} (ha : a ≠ 0) (v : DoubledSpace E) :
    IsMetricNull (a • v) ↔ IsMetricNull v := by
  unfold IsMetricNull
  simp [hessian_indefinite_form, KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right, ha]

lemma isMetricNull_sameRay_iff {v w : DoubledSpace E}
    (hvw : SameRayDoubled v w) :
    IsMetricNull v ↔ IsMetricNull w := by
  rcases hvw with ⟨a, ha, rfl⟩
  rw [isMetricNull_smul_iff ha]

/-- Metric-null rays, well-defined on the projective quotient. -/
def IsMetricNullRay : ProjectiveState E → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => IsMetricNull v)
    (by
      intro v w hvw
      exact propext (isMetricNull_sameRay_iff hvw))

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
