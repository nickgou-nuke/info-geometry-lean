import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Krein.Metric
import Mathlib.Tactic

section KreinClifford

variable {E : Type} [NormedAddCommGroup E]

section ProjectiveNull

section GradeNull

variable [NormedSpace ℝ E]

@[simp] lemma vacuum_def :
    vacuum (E := E) = projectivize (E := E) (0 : DoubledSpace E) := rfl

lemma inGradePlus_smul (a : ℝ) {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradePlus (E := E) (a • v) := by
  unfold inGradePlus at *
  calc
    modularJ (E := E) (a • v) = a • modularJ (E := E) v := by
      exact (modularJ (E := E)).map_smul a v
    _ = a • v := by
      rw [hv]

lemma inGradeMinus_smul (a : ℝ) {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradeMinus (E := E) (a • v) := by
  unfold inGradeMinus at *
  calc
    modularJ (E := E) (a • v) = a • modularJ (E := E) v := by
      exact (modularJ (E := E)).map_smul a v
    _ = a • (-v) := by
      rw [hv]
    _ = -(a • v) := by
      simp [smul_neg]

lemma inGradePlus_smul_iff {a : ℝ} (ha : a ≠ 0) (v : DoubledSpace E) :
    inGradePlus (E := E) (a • v) ↔ inGradePlus (E := E) v := by
  constructor
  · intro hv
    have : inGradePlus (E := E) (a⁻¹ • (a • v)) :=
      inGradePlus_smul (E := E) a⁻¹ hv
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro hv
    simpa using inGradePlus_smul (E := E) a hv

lemma inGradeMinus_smul_iff {a : ℝ} (ha : a ≠ 0) (v : DoubledSpace E) :
    inGradeMinus (E := E) (a • v) ↔ inGradeMinus (E := E) v := by
  constructor
  · intro hv
    have : inGradeMinus (E := E) (a⁻¹ • (a • v)) :=
      inGradeMinus_smul (E := E) a⁻¹ hv
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro hv
    simpa using inGradeMinus_smul (E := E) a hv

lemma inGradePlus_sameRay_iff {v w : DoubledSpace E}
    (hvw : SameRayDoubled (E := E) v w) :
    inGradePlus (E := E) v ↔ inGradePlus (E := E) w := by
  rcases hvw with ⟨a, ha, rfl⟩
  simpa using (inGradePlus_smul_iff (E := E) (v := v) ha).symm

lemma inGradeMinus_sameRay_iff {v w : DoubledSpace E}
    (hvw : SameRayDoubled (E := E) v w) :
    inGradeMinus (E := E) v ↔ inGradeMinus (E := E) w := by
  rcases hvw with ⟨a, ha, rfl⟩
  simpa using (inGradeMinus_smul_iff (E := E) (v := v) ha).symm

/-- Grade `+` rays, well-defined on the projective quotient. -/
def IsGradePlusRay : ProjectiveState (E := E) → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => inGradePlus (E := E) v)
    (by
      intro v w hvw
      exact propext (inGradePlus_sameRay_iff (E := E) (v := v) (w := w) hvw))

/-- Grade `-` rays, well-defined on the projective quotient. -/
def IsGradeMinusRay : ProjectiveState (E := E) → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => inGradeMinus (E := E) v)
    (by
      intro v w hvw
      exact propext (inGradeMinus_sameRay_iff (E := E) (v := v) (w := w) hvw))

@[simp] lemma IsGradePlusRay_projectivize (v : DoubledSpace E) :
    IsGradePlusRay (E := E) (projectivize (E := E) v) ↔ inGradePlus (E := E) v := Iff.rfl

@[simp] lemma IsGradeMinusRay_projectivize (v : DoubledSpace E) :
    IsGradeMinusRay (E := E) (projectivize (E := E) v) ↔ inGradeMinus (E := E) v := Iff.rfl

/-- “Grade-null” rays: points lying in either grading eigenspace. -/
def IsGradeNullRay (q : ProjectiveState (E := E)) : Prop :=
  IsGradePlusRay (E := E) q ∨ IsGradeMinusRay (E := E) q

lemma IsGradePlusRay_vacuum : IsGradePlusRay (E := E) (vacuum (E := E)) := by
  rw [vacuum_def, IsGradePlusRay_projectivize]
  simp [inGradePlus, modularJ]

lemma IsGradeMinusRay_vacuum : IsGradeMinusRay (E := E) (vacuum (E := E)) := by
  rw [vacuum_def, IsGradeMinusRay_projectivize]
  simp [inGradeMinus, modularJ]

lemma IsGradeNullRay_vacuum : IsGradeNullRay (E := E) (vacuum (E := E)) := by
  exact Or.inl (IsGradePlusRay_vacuum (E := E))

end GradeNull

section MetricNull

variable [InnerProductSpace ℝ E]

/-- “Metric-null” / isotropic doubled vectors for the neutral Hessian form. -/
def IsMetricNull (v : DoubledSpace E) : Prop :=
  hessianIndefiniteForm (E := E) v v = 0

lemma hessianIndefiniteForm_smul_smul (a b : ℝ) (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) (a • v) (b • w)
      = (a * b) * hessianIndefiniteForm (E := E) v w := by
  rcases v with ⟨x, ξ⟩
  rcases w with ⟨y, η⟩
  have h1 : inner ℝ (a • x) (b • η) = a * inner ℝ x (b • η) := by
    simpa using (real_inner_smul_left x (b • η) a)
  have h2 : inner ℝ x (b • η) = b * inner ℝ x η := by
    simpa using (real_inner_smul_right x η b)
  have h3 : inner ℝ (b • y) (a • ξ) = b * inner ℝ y (a • ξ) := by
    simpa using (real_inner_smul_left y (a • ξ) b)
  have h4 : inner ℝ y (a • ξ) = a * inner ℝ y ξ := by
    simpa using (real_inner_smul_right y ξ a)
  calc
    hessianIndefiniteForm (E := E) (a • (x, ξ)) (b • (y, η))
        = inner ℝ (a • x) (b • η) + inner ℝ (b • y) (a • ξ) := by rfl
    _ = a * inner ℝ x (b • η) + b * inner ℝ y (a • ξ) := by rw [h1, h3]
    _ = a * (b * inner ℝ x η) + b * (a * inner ℝ y ξ) := by rw [h2, h4]
    _ = (a * b) * (inner ℝ x η + inner ℝ y ξ) := by ring
    _ = (a * b) * hessianIndefiniteForm (E := E) (x, ξ) (y, η) := by rfl

lemma hessianIndefiniteForm_smul_left (a : ℝ) (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) (a • v) w
      = a * hessianIndefiniteForm (E := E) v w := by
  simpa using hessianIndefiniteForm_smul_smul (E := E) a 1 v w

lemma hessianIndefiniteForm_smul_right (a : ℝ) (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) v (a • w)
      = a * hessianIndefiniteForm (E := E) v w := by
  simpa [mul_comm] using hessianIndefiniteForm_smul_smul (E := E) 1 a v w

lemma hessianIndefiniteForm_self_smul (a : ℝ) (v : DoubledSpace E) :
    hessianIndefiniteForm (E := E) (a • v) (a • v)
      = (a ^ 2) * hessianIndefiniteForm (E := E) v v := by
  simpa [pow_two, mul_assoc] using
    hessianIndefiniteForm_smul_smul (E := E) a a v v

lemma isMetricNull_smul (a : ℝ) {v : DoubledSpace E}
    (hv : IsMetricNull (E := E) v) :
    IsMetricNull (E := E) (a • v) := by
  unfold IsMetricNull at *
  calc
    hessianIndefiniteForm (E := E) (a • v) (a • v)
        = (a * a) * hessianIndefiniteForm (E := E) v v := by
            exact hessianIndefiniteForm_smul_smul (E := E) a a v v
    _ = 0 := by simp [hv]

lemma isMetricNull_smul_iff (a : ℝ) (ha : a ≠ 0) (v : DoubledSpace E) :
    IsMetricNull (E := E) (a • v) ↔ IsMetricNull (E := E) v := by
  unfold IsMetricNull
  have hs :
      hessianIndefiniteForm (E := E) (a • v) (a • v)
        = (a * a) * hessianIndefiniteForm (E := E) v v := by
    exact hessianIndefiniteForm_smul_smul (E := E) a a v v
  constructor
  · intro h
    have hmul : (a * a) * hessianIndefiniteForm (E := E) v v = 0 := by
      simpa [hs] using h
    exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero ha ha)
  · intro h
    simp [hs, h]

lemma isMetricNull_sameRay_iff {v w : DoubledSpace E}
    (hvw : SameRayDoubled (E := E) v w) :
    IsMetricNull (E := E) v ↔ IsMetricNull (E := E) w := by
  rcases hvw with ⟨a, ha, rfl⟩
  simpa using (isMetricNull_smul_iff (E := E) a ha v).symm

/-- Metric-null rays, well-defined on the projective quotient. -/
def IsMetricNullRay : ProjectiveState (E := E) → Prop :=
  Quotient.lift
    (fun v : DoubledSpace E => IsMetricNull (E := E) v)
    (by
      intro v w hvw
      exact propext (isMetricNull_sameRay_iff (E := E) (v := v) (w := w) hvw))

@[simp] lemma IsMetricNullRay_projectivize (v : DoubledSpace E) :
    IsMetricNullRay (E := E) (projectivize (E := E) v) ↔ IsMetricNull (E := E) v := Iff.rfl

lemma IsMetricNullRay_vacuum : IsMetricNullRay (E := E) (vacuum (E := E)) := by
  rw [vacuum_def, IsMetricNullRay_projectivize]
  simp [IsMetricNull, hessianIndefiniteForm]

end MetricNull

section UnifiedNull

variable [InnerProductSpace ℝ E]

/-- Unified nullness on rays: vacuum, grade-null, or metric-null. -/
def IsNullRay (q : ProjectiveState (E := E)) : Prop :=
  q = vacuum (E := E) ∨
  IsGradeNullRay (E := E) q ∨
  IsMetricNullRay (E := E) q

end UnifiedNull

end ProjectiveNull

end KreinClifford
