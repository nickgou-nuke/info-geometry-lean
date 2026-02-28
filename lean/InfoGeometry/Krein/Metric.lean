import InfoGeometry.Clifford.Grading

section KreinClifford

variable {E : Type} [NormedAddCommGroup E]

section Metric

variable [InnerProductSpace ℝ E]

/-- Indefinite Hessian pairing on the doubled space. -/
def hessianIndefiniteForm (v w : DoubledSpace E) : ℝ :=
  inner ℝ v.1 w.2 + inner ℝ w.1 v.2

lemma hessianIndefiniteForm_symm (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) v w = hessianIndefiniteForm (E := E) w v := by
  simp [hessianIndefiniteForm, add_comm]

lemma hessianIndefiniteForm_isotropic_primal (x : E) :
    hessianIndefiniteForm (E := E) (x, (0 : E)) (x, (0 : E)) = 0 := by
  simp [hessianIndefiniteForm]

lemma hessianIndefiniteForm_isotropic_dual (ξ : E) :
    hessianIndefiniteForm (E := E) ((0 : E), ξ) ((0 : E), ξ) = 0 := by
  simp [hessianIndefiniteForm]

/-- Metric-preserving endomorphisms of the doubled neutral space. -/
def preservesMetric (U : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ v w, hessianIndefiniteForm (E := E) (U v) (U w) = hessianIndefiniteForm (E := E) v w

/-- Metric-reversing endomorphisms of the doubled neutral space. -/
def antiPreservesMetric (U : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ v w, hessianIndefiniteForm (E := E) (U v) (U w) = -hessianIndefiniteForm (E := E) v w

/-- Infinitesimal isometries for the neutral Hessian form (Lie algebra condition). -/
def IsInfinitesimalIsometry (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ v w,
    hessianIndefiniteForm (E := E) (A v) w +
      hessianIndefiniteForm (E := E) v (A w) = 0

lemma infinitesimalIsometry_zero :
    IsInfinitesimalIsometry (E := E) (0 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  intro v w
  simp [hessianIndefiniteForm]

lemma infinitesimalIsometry_add
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B) :
    IsInfinitesimalIsometry (E := E) (A + B) := by
  intro v w
  calc
    hessianIndefiniteForm (E := E) ((A + B) v) w
      + hessianIndefiniteForm (E := E) v ((A + B) w)
        = (hessianIndefiniteForm (E := E) (A v) w
            + hessianIndefiniteForm (E := E) v (A w))
          + (hessianIndefiniteForm (E := E) (B v) w
              + hessianIndefiniteForm (E := E) v (B w)) := by
                simp [ContinuousLinearMap.add_apply, hessianIndefiniteForm,
                  inner_add_left, inner_add_right]
                ring
    _ = 0 + 0 := by rw [hA v w, hB v w]
    _ = 0 := by ring

lemma infinitesimalIsometry_smul
    (a : ℝ)
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A) :
    IsInfinitesimalIsometry (E := E) (a • A) := by
  intro v w
  have h1 : inner ℝ (a • (A v).1) w.2 = a * inner ℝ (A v).1 w.2 := by
    simpa using (real_inner_smul_left (A v).1 w.2 a)
  have h2 : inner ℝ w.1 (a • (A v).2) = a * inner ℝ w.1 (A v).2 := by
    simpa using (real_inner_smul_right w.1 (A v).2 a)
  have h3 : inner ℝ v.1 (a • (A w).2) = a * inner ℝ v.1 (A w).2 := by
    simpa using (real_inner_smul_right v.1 (A w).2 a)
  have h4 : inner ℝ (a • (A w).1) v.2 = a * inner ℝ (A w).1 v.2 := by
    simpa using (real_inner_smul_left (A w).1 v.2 a)
  calc
    hessianIndefiniteForm (E := E) ((a • A) v) w
      + hessianIndefiniteForm (E := E) v ((a • A) w)
        = inner ℝ (a • (A v).1) w.2 + inner ℝ w.1 (a • (A v).2)
          + (inner ℝ v.1 (a • (A w).2) + inner ℝ (a • (A w).1) v.2) := by
              simp [ContinuousLinearMap.smul_apply, hessianIndefiniteForm, add_assoc]
    _ = a * inner ℝ (A v).1 w.2 + a * inner ℝ w.1 (A v).2
          + (a * inner ℝ v.1 (A w).2 + a * inner ℝ (A w).1 v.2) := by
            simp [h1, h2, h3, h4]
    _ = a *
          (hessianIndefiniteForm (E := E) (A v) w
            + hessianIndefiniteForm (E := E) v (A w)) := by
            simp [hessianIndefiniteForm]
            ring
    _ = a * 0 := by rw [hA v w]
    _ = 0 := by ring

lemma preservesMetric_id :
    preservesMetric (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  intro v w
  simp

lemma preservesMetric_comp
    {U V : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hU : preservesMetric (E := E) U)
    (hV : preservesMetric (E := E) V) :
    preservesMetric (E := E) (U.comp V) := by
  intro v w
  calc
    hessianIndefiniteForm (E := E) ((U.comp V) v) ((U.comp V) w)
        = hessianIndefiniteForm (E := E) (U (V v)) (U (V w)) := by rfl
    _ = hessianIndefiniteForm (E := E) (V v) (V w) := hU (V v) (V w)
    _ = hessianIndefiniteForm (E := E) v w := hV v w

lemma antiPreservesMetric_comp
    {U V : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hU : antiPreservesMetric (E := E) U)
    (hV : antiPreservesMetric (E := E) V) :
    preservesMetric (E := E) (U.comp V) := by
  intro v w
  calc
    hessianIndefiniteForm (E := E) ((U.comp V) v) ((U.comp V) w)
        = hessianIndefiniteForm (E := E) (U (V v)) (U (V w)) := by rfl
    _ = -hessianIndefiniteForm (E := E) (V v) (V w) := hU (V v) (V w)
    _ = -(-hessianIndefiniteForm (E := E) v w) := by rw [hV v w]
    _ = hessianIndefiniteForm (E := E) v w := by ring

lemma preservesMetric_comp_anti
    {U V : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hU : preservesMetric (E := E) U)
    (hV : antiPreservesMetric (E := E) V) :
    antiPreservesMetric (E := E) (U.comp V) := by
  intro v w
  calc
    hessianIndefiniteForm (E := E) ((U.comp V) v) ((U.comp V) w)
        = hessianIndefiniteForm (E := E) (U (V v)) (U (V w)) := by rfl
    _ = hessianIndefiniteForm (E := E) (V v) (V w) := hU (V v) (V w)
    _ = -hessianIndefiniteForm (E := E) v w := hV v w

lemma antiPreservesMetric_comp_preserves
    {U V : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hU : antiPreservesMetric (E := E) U)
    (hV : preservesMetric (E := E) V) :
    antiPreservesMetric (E := E) (U.comp V) := by
  intro v w
  calc
    hessianIndefiniteForm (E := E) ((U.comp V) v) ((U.comp V) w)
        = hessianIndefiniteForm (E := E) (U (V v)) (U (V w)) := by rfl
    _ = -hessianIndefiniteForm (E := E) (V v) (V w) := hU (V v) (V w)
    _ = -hessianIndefiniteForm (E := E) v w := by rw [hV v w]

lemma preservesMetric_symm
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)) :
    preservesMetric (E := E) (U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  intro v w
  have h := hU (U.symm v) (U.symm w)
  simpa using h.symm

lemma modularJ_preservesMetric :
    preservesMetric (E := E) (modularJ (E := E)) := by
  intro v w
  simp [hessianIndefiniteForm, modularJ, real_inner_comm, add_comm]

lemma spectralEpsilon_antiPreservesMetric :
    antiPreservesMetric (E := E) (spectralEpsilon (E := E)) := by
  intro v w
  simp [hessianIndefiniteForm, spectralEpsilon]
  ring

lemma spectralEpsilon_infinitesimalIsometry :
    IsInfinitesimalIsometry (E := E) (spectralEpsilon (E := E)) := by
  intro v w
  simp [hessianIndefiniteForm, spectralEpsilon]
  ring

lemma infinitesimalIsometry_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A)
    (hB : IsInfinitesimalIsometry (E := E) B) :
    IsInfinitesimalIsometry (E := E) (clmComm A B) := by
  intro v w
  have hsplit₁ :
      hessianIndefiniteForm (E := E) ((clmComm A B) v) w
        = hessianIndefiniteForm (E := E) (A (B v)) w
          - hessianIndefiniteForm (E := E) (B (A v)) w := by
    simp [clmComm, hessianIndefiniteForm, sub_eq_add_neg,
      inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      add_assoc, add_left_comm, add_comm]
  have hsplit₂ :
      hessianIndefiniteForm (E := E) v ((clmComm A B) w)
        = hessianIndefiniteForm (E := E) v (A (B w))
          - hessianIndefiniteForm (E := E) v (B (A w)) := by
    simp [clmComm, hessianIndefiniteForm, sub_eq_add_neg,
      inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      add_assoc, add_left_comm, add_comm]
  have hA1 : hessianIndefiniteForm (E := E) (A (B v)) w
      = -hessianIndefiniteForm (E := E) (B v) (A w) := by
    linarith [hA (B v) w]
  have hB1 : hessianIndefiniteForm (E := E) (B (A v)) w
      = -hessianIndefiniteForm (E := E) (A v) (B w) := by
    linarith [hB (A v) w]
  have hA2 : hessianIndefiniteForm (E := E) v (A (B w))
      = -hessianIndefiniteForm (E := E) (A v) (B w) := by
    linarith [hA v (B w)]
  have hB2 : hessianIndefiniteForm (E := E) v (B (A w))
      = -hessianIndefiniteForm (E := E) (B v) (A w) := by
    linarith [hB v (A w)]
  rw [hsplit₁, hsplit₂, hA1, hB1, hA2, hB2]
  ring

/-- Lie subalgebra of infinitesimal isometries of the neutral Hessian form. -/
def kreinLieSubalgebra :
    LieSubalgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) where
  carrier := {A | IsInfinitesimalIsometry (E := E) A}
  zero_mem' := infinitesimalIsometry_zero (E := E)
  add_mem' := by
    intro A B hA hB
    exact infinitesimalIsometry_add (E := E) hA hB
  smul_mem' := by
    intro a A hA
    exact infinitesimalIsometry_smul (E := E) a hA
  lie_mem' := by
    intro A B hA hB
    change IsInfinitesimalIsometry (E := E) (clmComm A B)
    exact infinitesimalIsometry_closed_comm (E := E) hA hB

end Metric

end KreinClifford
