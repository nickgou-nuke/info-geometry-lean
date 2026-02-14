import InfoGeometry.Clifford.Grading
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Metric

variable [InnerProductSpace ℝ E]

/-- Indefinite Hessian pairing on the doubled space. -/
def hessianIndefiniteForm (v w : DoubledSpace E) : ℝ :=
  inner ℝ v.1 w.2 + inner ℝ w.1 v.2

omit [NormedSpace ℝ E] in
lemma hessianIndefiniteForm_symm (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) v w = hessianIndefiniteForm (E := E) w v := by
  simp [hessianIndefiniteForm, add_comm]

omit [NormedSpace ℝ E] in
lemma hessianIndefiniteForm_isotropic_primal (x : E) :
    hessianIndefiniteForm (E := E) (x, (0 : E)) (x, (0 : E)) = 0 := by
  simp [hessianIndefiniteForm]

omit [NormedSpace ℝ E] in
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

/-- Continuous automorphisms preserving the neutral Hessian pairing. -/
structure KreinIsometry where
  U : DoubledSpace E ≃L[ℝ] DoubledSpace E
  isometry : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Continuous automorphisms reversing the neutral Hessian pairing. -/
structure KreinAntiIsometry where
  U : DoubledSpace E ≃L[ℝ] DoubledSpace E
  antiIsometry : antiPreservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Orthogonal isometries of the doubled neutral form `hessianIndefiniteForm`
(`O(hessianIndefiniteForm)`, finite-dimensional model of `O(n,n)`). -/
def HessianOrthogonalGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℝ E] : Type _ :=
  {U : DoubledSpace E ≃L[ℝ] DoubledSpace E //
    preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)}

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

lemma preservesMetric_symm
    (U : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E)) :
    preservesMetric (E := E) (U.symm : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  intro v w
  have h := hU (U.symm v) (U.symm w)
  simpa using h.symm

lemma preservesMetric_equiv_comp
    (U V : DoubledSpace E ≃L[ℝ] DoubledSpace E)
    (hU : preservesMetric (E := E) (U : DoubledSpace E →L[ℝ] DoubledSpace E))
    (hV : preservesMetric (E := E) (V : DoubledSpace E →L[ℝ] DoubledSpace E)) :
    preservesMetric (E := E)
      ((U : DoubledSpace E →L[ℝ] DoubledSpace E).comp
        (V : DoubledSpace E →L[ℝ] DoubledSpace E)) := by
  exact preservesMetric_comp (E := E) hU hV

def HessianOrthogonalGroup.one : HessianOrthogonalGroup E :=
  ⟨ContinuousLinearEquiv.refl ℝ (DoubledSpace E), preservesMetric_id (E := E)⟩

def HessianOrthogonalGroup.comp
    (U V : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E := by
  refine ⟨U.1.trans V.1, ?_⟩
  intro v w
  change hessianIndefiniteForm (E := E) (V.1 (U.1 v)) (V.1 (U.1 w))
      = hessianIndefiniteForm (E := E) v w
  calc
    hessianIndefiniteForm (E := E) (V.1 (U.1 v)) (V.1 (U.1 w))
        = hessianIndefiniteForm (E := E) (U.1 v) (U.1 w) := V.2 (U.1 v) (U.1 w)
    _ = hessianIndefiniteForm (E := E) v w := U.2 v w

def HessianOrthogonalGroup.inv
    (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  ⟨U.1.symm, preservesMetric_symm (E := E) U.1 U.2⟩

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

/-- Swap involution as a continuous linear equivalence. -/
def modularJEquiv : DoubledSpace E ≃L[ℝ] DoubledSpace E where
  toLinearEquiv :=
    { toFun := fun v => (v.2, v.1)
      invFun := fun v => (v.2, v.1)
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_add' := by intro v w; simp
      map_smul' := by intro a v; simp }
  continuous_toFun := by continuity
  continuous_invFun := by continuity

/-- Sign involution as a continuous linear equivalence. -/
def spectralEpsilonEquiv : DoubledSpace E ≃L[ℝ] DoubledSpace E where
  toLinearEquiv :=
    { toFun := fun v => (v.1, -v.2)
      invFun := fun v => (v.1, -v.2)
      left_inv := by intro v; simp
      right_inv := by intro v; simp
      map_add' := by intro v w; simp [add_comm]
      map_smul' := by intro a v; simp [smul_neg] }
  continuous_toFun := by continuity
  continuous_invFun := by continuity

def modularJKreinIsometry : KreinIsometry (E := E) where
  U := modularJEquiv (E := E)
  isometry := by
    simpa [modularJEquiv] using modularJ_preservesMetric (E := E)

def modularJHessianOrthogonal : HessianOrthogonalGroup E :=
  ⟨modularJEquiv (E := E), by
    simpa [modularJEquiv] using modularJ_preservesMetric (E := E)⟩

def spectralEpsilonKreinAntiIsometry : KreinAntiIsometry (E := E) where
  U := spectralEpsilonEquiv (E := E)
  antiIsometry := by
    simpa [spectralEpsilonEquiv] using spectralEpsilon_antiPreservesMetric (E := E)

end Metric

end KreinClifford
