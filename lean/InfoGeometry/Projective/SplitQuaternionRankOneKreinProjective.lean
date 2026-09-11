import InfoGeometry.Quantum.NeutralKreinMajoranaFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A real doubled Krein realization of the rank-one split flow

This owner uses the existing doubled real carrier `Fin 2 ⊕ Fin 2`.  It
defines an internal complex structure, a neutral `(2,2)` form, and a commuting
hyperbolic involution by explicit real block matrices.  The two displayed root
vectors are genuine null eigenvectors with nonzero mutual pairing.

The projective state is represented by equality of genuine real `J`-invariant
two-planes; no complexification or thermodynamic interpretation is introduced.
-/

namespace InfoGeometry.Projective.SplitQuaternionRankOneKreinProjective

open Matrix
open InfoGeometry.Quantum.NeutralKreinMajoranaFrame

abbrev Index := Carrier 2
abbrev Mat4R := InfoGeometry.Quantum.NeutralKreinMajoranaFrame.DoubledMat4R
abbrev Vec4R := Index → ℝ

/-- The `(1,1)` metric on either real half. -/
def halfMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 0; 0, -1]

/-- The hyperbolic rank-one generator on either real half. -/
def halfBoost : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), 1; 1, 0]

/-- Neutral metric of signature `(2,2)` in the doubled real coordinates. -/
def kreinMetric22 : Mat4R :=
  Matrix.fromBlocks halfMetric 0 0 halfMetric

/-- Internal real complex structure. -/
def internalJ : Mat4R :=
  majoranaForm 2

/-- The real hyperbolic axis, duplicated on the two `J`-related halves. -/
def ellAxis : Mat4R :=
  Matrix.fromBlocks halfBoost 0 0 halfBoost

theorem internalJ_sq :
    internalJ * internalJ = -(1 : Mat4R) := by
  exact majoranaForm_squared 2

theorem ellAxis_sq :
    ellAxis * ellAxis = (1 : Mat4R) := by
  rw [ellAxis, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfBoost, Matrix.fromBlocks]

theorem internalJ_ellAxis_commute :
    internalJ * ellAxis = ellAxis * internalJ := by
  rw [internalJ, majoranaForm, ellAxis,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfBoost, Matrix.fromBlocks]

theorem internalJ_preserves_kreinMetric22 :
    internalJ.transpose * kreinMetric22 * internalJ = kreinMetric22 := by
  rw [internalJ, majoranaForm, kreinMetric22,
    Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfMetric, Matrix.fromBlocks]

theorem ellAxis_is_kreinSkew :
    ellAxis.transpose * kreinMetric22 + kreinMetric22 * ellAxis = 0 := by
  rw [ellAxis, kreinMetric22, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfMetric, halfBoost, Matrix.fromBlocks,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Positive root representative in the first real half. -/
def rootPlus : Vec4R
  | Sum.inl 0 => 1
  | Sum.inl 1 => 1
  | Sum.inr _ => 0

/-- Negative root representative in the first real half. -/
def rootMinus : Vec4R
  | Sum.inl 0 => 1
  | Sum.inl 1 => -1
  | Sum.inr _ => 0

theorem ellAxis_rootPlus :
    ellAxis.mulVec rootPlus = rootPlus := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [ellAxis, halfBoost, rootPlus, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem ellAxis_rootMinus :
    ellAxis.mulVec rootMinus = -rootMinus := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [ellAxis, halfBoost, rootMinus, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Fintype.sum_sum_type, Fin.sum_univ_two]

/-- Bilinear pairing defined by the concrete neutral metric. -/
def kreinPair (x y : Vec4R) : ℝ :=
  dotProduct x (kreinMetric22.mulVec y)

theorem rootPlus_null : kreinPair rootPlus rootPlus = 0 := by
  simp [kreinPair, kreinMetric22, halfMetric, rootPlus,
    Matrix.mulVec, dotProduct, Matrix.fromBlocks,
    Fintype.sum_sum_type, Fin.sum_univ_two]

theorem rootMinus_null : kreinPair rootMinus rootMinus = 0 := by
  simp [kreinPair, kreinMetric22, halfMetric, rootMinus,
    Matrix.mulVec, dotProduct, Matrix.fromBlocks,
    Fintype.sum_sum_type, Fin.sum_univ_two]

theorem root_pairing : kreinPair rootPlus rootMinus = 2 := by
  norm_num [kreinPair, kreinMetric22, halfMetric, rootPlus, rootMinus,
    Matrix.mulVec, dotProduct, Matrix.fromBlocks,
    Fintype.sum_sum_type, Fin.sum_univ_two]

/-- The internal complex structure and the hyperbolic axis acting on vectors. -/
def JAction : Vec4R →ₗ[ℝ] Vec4R := Matrix.mulVecLin internalJ

def ellAction : Vec4R →ₗ[ℝ] Vec4R := Matrix.mulVecLin ellAxis

theorem JAction_sq (x : Vec4R) : JAction (JAction x) = -x := by
  simp only [JAction, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, internalJ_sq]
  rw [show (-1 : Mat4R) = -(1 : Mat4R) by rfl, Matrix.neg_mulVec,
    Matrix.one_mulVec]

theorem ellAction_sq (x : Vec4R) : ellAction (ellAction x) = x := by
  simp only [ellAction, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, ellAxis_sq]
  simp

theorem JAction_ellAction_commute (x : Vec4R) :
    JAction (ellAction x) = ellAction (JAction x) := by
  simpa [JAction, ellAction, Matrix.mulVecLin_apply] using
    congrArg (fun M : Mat4R => M.mulVec x) internalJ_ellAxis_commute

/-- Closed hyperbolic flow generated by the involutive rank-one axis. -/
noncomputable def halfBoostFlow (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh t, Real.sinh t; Real.sinh t, Real.cosh t]

noncomputable def ellFlow (t : ℝ) : Mat4R :=
  Matrix.fromBlocks (halfBoostFlow t) 0 0 (halfBoostFlow t)

theorem halfBoostFlow_krein_isometry (t : ℝ) :
    (halfBoostFlow t).transpose * halfMetric * halfBoostFlow t = halfMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfBoostFlow, halfMetric, Matrix.mul_apply, Fin.sum_univ_two]
    <;> nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem ellFlow_krein_isometry (t : ℝ) :
    (ellFlow t).transpose * kreinMetric22 * ellFlow t = kreinMetric22 := by
  rw [ellFlow, kreinMetric22, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfBoostFlow, halfMetric, Matrix.fromBlocks,
      Matrix.mul_apply, Fin.sum_univ_two]
    <;> nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem halfBoostFlow_add (s t : ℝ) :
    halfBoostFlow (s + t) = halfBoostFlow s * halfBoostFlow t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfBoostFlow, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cosh_add, Real.sinh_add]
    <;> ring

theorem ellFlow_add (s t : ℝ) :
    ellFlow (s + t) = ellFlow s * ellFlow t := by
  rw [ellFlow, ellFlow, ellFlow, Matrix.fromBlocks_multiply,
    halfBoostFlow_add]
  simp

theorem ellFlow_zero : ellFlow 0 = (1 : Mat4R) := by
  rw [ellFlow]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfBoostFlow, Matrix.fromBlocks, Real.cosh_zero, Real.sinh_zero]

theorem ellFlow_inverse (t : ℝ) : ellFlow (-t) * ellFlow t = (1 : Mat4R) := by
  rw [← ellFlow_add, neg_add_cancel, ellFlow_zero]

theorem internalJ_ellFlow_commute (t : ℝ) :
    internalJ * ellFlow t = ellFlow t * internalJ := by
  rw [internalJ, majoranaForm, ellFlow,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [halfBoostFlow, Matrix.fromBlocks, Matrix.mul_apply,
      Fin.sum_univ_two]
    <;> ring

noncomputable def ellFlowAction (t : ℝ) : Vec4R →ₗ[ℝ] Vec4R :=
  Matrix.mulVecLin (ellFlow t)

theorem ellFlowAction_apply (t : ℝ) (x : Vec4R) :
    ellFlowAction t x = (ellFlow t).mulVec x :=
  rfl

theorem ellFlowAction_add (s t : ℝ) (x : Vec4R) :
    ellFlowAction (s + t) x = ellFlowAction s (ellFlowAction t x) := by
  simp only [ellFlowAction, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, ellFlow_add]

theorem ellFlowAction_inverse_left (t : ℝ) (x : Vec4R) :
    ellFlowAction (-t) (ellFlowAction t x) = x := by
  simp only [ellFlowAction, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, ellFlow_inverse]
  simp

theorem ellFlowAction_JAction_commute (t : ℝ) (x : Vec4R) :
    ellFlowAction t (JAction x) = JAction (ellFlowAction t x) := by
  simp only [ellFlowAction, JAction, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    internalJ_ellFlow_commute]

def halfRootPlus : Fin 2 → ℝ := ![(1 : ℝ), 1]

def halfRootMinus : Fin 2 → ℝ := ![(1 : ℝ), -1]

theorem halfBoostFlow_rootPlus (t : ℝ) :
    (halfBoostFlow t).mulVec halfRootPlus =
      Real.exp t • halfRootPlus := by
  funext i
  fin_cases i <;>
    simp [halfBoostFlow, halfRootPlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    <;> nlinarith [Real.cosh_add_sinh t]

theorem halfBoostFlow_rootMinus (t : ℝ) :
    (halfBoostFlow t).mulVec halfRootMinus =
      Real.exp (-t) • halfRootMinus := by
  funext i
  fin_cases i <;>
    simp [halfBoostFlow, halfRootMinus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    <;> nlinarith [Real.cosh_sub_sinh t]

/-- The real two-plane carrying one internally complex projective direction. -/
def jPlane (v : Vec4R) : Submodule ℝ Vec4R :=
  Submodule.span ℝ ({v, JAction v} : Set Vec4R)

def jPlaneFamily (v : Vec4R) : Fin 2 → Vec4R :=
  ![v, JAction v]

theorem jPlaneFamily_linearIndependent {v : Vec4R} (hv : v ≠ 0) :
    LinearIndependent ℝ (jPlaneFamily v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hcoord : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  rcases hcoord with ⟨j, hj⟩
  have hsum := congrArg (fun z : Vec4R => z j) hg
  have hsumJ := congrArg (fun z : Vec4R => (JAction z) j) hg
  have h0 : g 0 * v j + g 1 * (JAction v) j = 0 := by
    simpa [jPlaneFamily, Fin.sum_univ_two, smul_eq_mul] using hsum
  have h1 : g 0 * (JAction v) j - g 1 * v j = 0 := by
    simpa [jPlaneFamily, Fin.sum_univ_two, smul_eq_mul, map_add,
      map_smul, JAction_sq] using hsumJ
  have hdet : 0 < (v j) ^ 2 + (JAction v j) ^ 2 := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hj)
      (sq_nonneg _)
  have hg0 : g 0 * ((v j) ^ 2 + (JAction v j) ^ 2) = 0 := by
    have h0' : (v j) * (g 0 * v j + g 1 * (JAction v) j) = 0 := by
      rw [h0, mul_zero]
    have h1' : (JAction v j) * (g 0 * (JAction v) j - g 1 * v j) = 0 := by
      rw [h1, mul_zero]
    calc
      g 0 * ((v j) ^ 2 + (JAction v j) ^ 2) =
          (v j) * (g 0 * v j + g 1 * (JAction v) j) +
            (JAction v j) * (g 0 * (JAction v) j - g 1 * v j) := by ring
      _ = 0 := by rw [h0', h1']; ring
  have hg1 : g 1 * ((v j) ^ 2 + (JAction v j) ^ 2) = 0 := by
    have h0' : (JAction v j) * (g 0 * v j + g 1 * (JAction v) j) = 0 := by
      rw [h0, mul_zero]
    have h1' : (v j) * (g 0 * (JAction v) j - g 1 * v j) = 0 := by
      rw [h1, mul_zero]
    calc
      g 1 * ((v j) ^ 2 + (JAction v j) ^ 2) =
          (JAction v j) * (g 0 * v j + g 1 * (JAction v) j) -
            (v j) * (g 0 * (JAction v) j - g 1 * v j) := by ring
      _ = 0 := by rw [h0', h1']; ring
  fin_cases i
  · exact (mul_eq_zero.mp hg0).resolve_right (ne_of_gt hdet)
  · exact (mul_eq_zero.mp hg1).resolve_right (ne_of_gt hdet)

theorem jPlane_finrank {v : Vec4R} (hv : v ≠ 0) :
    Module.finrank ℝ (jPlane v) = 2 := by
  have hli : LinearIndependent ℝ (jPlaneFamily v) :=
    jPlaneFamily_linearIndependent hv
  have hrange : Set.range (jPlaneFamily v) =
      ({v, JAction v} : Set Vec4R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [jPlaneFamily]
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp [jPlaneFamily]⟩
      · exact ⟨1, by simp [jPlaneFamily]⟩
  change Module.finrank ℝ
      (Submodule.span ℝ ({v, JAction v} : Set Vec4R)) = 2
  rw [← hrange]
  rw [finrank_span_eq_card hli]
  simp

theorem JAction_mem_jPlane (v : Vec4R) : JAction v ∈ jPlane v := by
  exact Submodule.subset_span (by simp)

theorem jPlane_JAction (v : Vec4R) : jPlane (JAction v) = jPlane v := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact JAction_mem_jPlane v
    · subst x
      rw [JAction_sq]
      exact Submodule.neg_mem (jPlane v) (Submodule.subset_span (by simp))
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · subst x
      have hmem : JAction (JAction v) ∈ jPlane (JAction v) :=
        Submodule.subset_span (by simp)
      rw [JAction_sq] at hmem
      simpa using (Submodule.neg_mem (jPlane (JAction v)) hmem)
    · subst x
      exact Submodule.subset_span (by simp)

theorem ellAction_mem_jPlane_ell (v x : Vec4R) (hx : x ∈ jPlane v) :
    ellAction x ∈ jPlane (ellAction v) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with hx | hx
    · subst x
      simpa using Submodule.subset_span
        (show ellAction v ∈ ({ellAction v, JAction (ellAction v)} : Set Vec4R) by simp)
    · subst x
      rw [← JAction_ellAction_commute]
      simpa using Submodule.subset_span
        (show JAction (ellAction v) ∈
          ({ellAction v, JAction (ellAction v)} : Set Vec4R) by simp)
  · simpa using (jPlane (ellAction v)).zero_mem
  · intro x y hx hy hx' hy'
    simpa [map_add] using (jPlane (ellAction v)).add_mem hx' hy'
  · intro a x hx hx'
    simpa [map_smul] using (jPlane (ellAction v)).smul_mem a hx'

theorem ellAction_preserves_jPlane_eq {v w : Vec4R}
    (h : jPlane v = jPlane w) :
    jPlane (ellAction v) = jPlane (ellAction w) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · subst x
      have hv : v ∈ jPlane w := by
        rw [← h]
        exact Submodule.subset_span (by simp)
      exact ellAction_mem_jPlane_ell w v hv
    · subst x
      have hv : JAction v ∈ jPlane w := by
        rw [← h]
        exact JAction_mem_jPlane v
      simpa [JAction_ellAction_commute] using ellAction_mem_jPlane_ell w (JAction v) hv
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · subst x
      have hw : w ∈ jPlane v := by
        rw [h]
        exact Submodule.subset_span (by simp)
      exact ellAction_mem_jPlane_ell v w hw
    · subst x
      have hw : JAction w ∈ jPlane v := by
        rw [h]
        exact JAction_mem_jPlane w
      simpa [JAction_ellAction_commute] using ellAction_mem_jPlane_ell v (JAction w) hw

theorem ellFlowAction_mem_jPlane (t : ℝ) (v x : Vec4R)
    (hx : x ∈ jPlane v) :
    ellFlowAction t x ∈ jPlane (ellFlowAction t v) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with hx | hx
    · subst x
      exact Submodule.subset_span (by simp)
    · subst x
      rw [ellFlowAction_JAction_commute]
      exact Submodule.subset_span (by simp)
  · simpa using (jPlane (ellFlowAction t v)).zero_mem
  · intro x y hx hy hx' hy'
    simpa [map_add] using (jPlane (ellFlowAction t v)).add_mem hx' hy'
  · intro a x hx hx'
    simpa [map_smul] using (jPlane (ellFlowAction t v)).smul_mem a hx'

theorem ellFlowAction_preserves_jPlane_eq {v w : Vec4R}
    (t : ℝ) (h : jPlane v = jPlane w) :
    jPlane (ellFlowAction t v) = jPlane (ellFlowAction t w) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · subst x
      have hv : v ∈ jPlane w := by
        rw [← h]
        exact Submodule.subset_span (by simp)
      exact ellFlowAction_mem_jPlane t w v hv
    · subst x
      have hv : JAction v ∈ jPlane w := by
        rw [← h]
        exact JAction_mem_jPlane v
      simpa [ellFlowAction_JAction_commute] using
        ellFlowAction_mem_jPlane t w (JAction v) hv
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · subst x
      have hw : w ∈ jPlane v := by
        rw [h]
        exact Submodule.subset_span (by simp)
      exact ellFlowAction_mem_jPlane t v w hw
    · subst x
      have hw : JAction w ∈ jPlane v := by
        rw [h]
        exact JAction_mem_jPlane w
      simpa [ellFlowAction_JAction_commute] using
        ellFlowAction_mem_jPlane t v (JAction w) hw

/-- Two nonzero representatives define the same internally complex projective ray. -/
def sameJPlane (v w : {x : Vec4R // x ≠ 0}) : Prop :=
  jPlane v.1 = jPlane w.1

instance : Setoid {x : Vec4R // x ≠ 0} where
  r := sameJPlane
  iseqv := ⟨by intro v; rfl, by intro v w h; exact h.symm,
    by intro u v w huv hvw; exact huv.trans hvw⟩

abbrev JProjectiveState :=
  Quotient (inferInstance : Setoid {x : Vec4R // x ≠ 0})

def JProjectivize (v : {x : Vec4R // x ≠ 0}) : JProjectiveState :=
  Quotient.mk _ v

theorem JProjectivize_eq_iff (v w : {x : Vec4R // x ≠ 0}) :
    JProjectivize v = JProjectivize w ↔ sameJPlane v w := by
  exact Quotient.eq

theorem ellAction_ne_zero {v : Vec4R} (hv : v ≠ 0) : ellAction v ≠ 0 := by
  intro h
  have h' := congrArg ellAction h
  exact hv (by simpa [ellAction_sq] using h')

def ellProjectiveAction : JProjectiveState → JProjectiveState :=
  Quotient.lift
    (fun v : {x : Vec4R // x ≠ 0} =>
      Quotient.mk _ ⟨ellAction v.1, ellAction_ne_zero v.2⟩)
    (by
      intro v w h
      apply Quotient.sound
      exact ellAction_preserves_jPlane_eq h)

theorem ellProjectiveAction_apply (v : {x : Vec4R // x ≠ 0}) :
    ellProjectiveAction (JProjectivize v) =
      JProjectivize ⟨ellAction v.1, ellAction_ne_zero v.2⟩ := by
  rfl

theorem ellProjectiveAction_involutive (v : {x : Vec4R // x ≠ 0}) :
    ellProjectiveAction (ellProjectiveAction (JProjectivize v)) =
      JProjectivize v := by
  rw [ellProjectiveAction_apply, ellProjectiveAction_apply]
  apply (JProjectivize_eq_iff _ _).2
  dsimp [sameJPlane]
  rw [ellAction_sq]

theorem ellFlowAction_ne_zero {t : ℝ} {v : Vec4R} (hv : v ≠ 0) :
    ellFlowAction t v ≠ 0 := by
  intro h
  have h' := congrArg (ellFlowAction (-t)) h
  exact hv (by simpa [ellFlowAction_inverse_left] using h')

noncomputable def ellFlowProjectiveAction (t : ℝ) :
    JProjectiveState → JProjectiveState :=
  Quotient.lift
    (fun v : {x : Vec4R // x ≠ 0} =>
      Quotient.mk _ ⟨ellFlowAction t v.1, ellFlowAction_ne_zero v.2⟩)
    (by
      intro v w h
      apply Quotient.sound
      exact ellFlowAction_preserves_jPlane_eq t h)

theorem ellFlowProjectiveAction_apply (t : ℝ)
    (v : {x : Vec4R // x ≠ 0}) :
    ellFlowProjectiveAction t (JProjectivize v) =
      JProjectivize ⟨ellFlowAction t v.1, ellFlowAction_ne_zero v.2⟩ :=
  rfl

theorem ellFlowProjectiveAction_add (s t : ℝ) :
    ellFlowProjectiveAction (s + t) =
      ellFlowProjectiveAction s ∘ ellFlowProjectiveAction t := by
  funext p
  refine Quotient.inductionOn p ?_
  intro v
  change ellFlowProjectiveAction (s + t) (JProjectivize v) =
    ellFlowProjectiveAction s
      (ellFlowProjectiveAction t (JProjectivize v))
  rw [ellFlowProjectiveAction_apply, ellFlowProjectiveAction_apply,
    ellFlowProjectiveAction_apply]
  apply (JProjectivize_eq_iff _ _).2
  dsimp [sameJPlane]
  rw [ellFlowAction_add]

theorem ellFlowProjectiveAction_zero :
    ellFlowProjectiveAction 0 = id := by
  funext p
  refine Quotient.inductionOn p ?_
  intro v
  change ellFlowProjectiveAction 0 (JProjectivize v) = JProjectivize v
  rw [ellFlowProjectiveAction_apply]
  apply (JProjectivize_eq_iff _ _).2
  dsimp [sameJPlane]
  simp [ellFlowAction, ellFlow_zero]

theorem ellFlowProjectiveAction_inverse_left (t : ℝ) :
    ellFlowProjectiveAction (-t) ∘ ellFlowProjectiveAction t = id := by
  funext p
  refine Quotient.inductionOn p ?_
  intro v
  change ellFlowProjectiveAction (-t)
      (ellFlowProjectiveAction t (JProjectivize v)) = JProjectivize v
  rw [ellFlowProjectiveAction_apply, ellFlowProjectiveAction_apply]
  apply (JProjectivize_eq_iff _ _).2
  dsimp [sameJPlane]
  rw [ellFlowAction_inverse_left]

theorem ellFlowProjectiveAction_inverse_right (t : ℝ) :
    ellFlowProjectiveAction t ∘ ellFlowProjectiveAction (-t) = id := by
  funext p
  refine Quotient.inductionOn p ?_
  intro v
  change ellFlowProjectiveAction t
      (ellFlowProjectiveAction (-t) (JProjectivize v)) = JProjectivize v
  rw [ellFlowProjectiveAction_apply, ellFlowProjectiveAction_apply]
  apply (JProjectivize_eq_iff _ _).2
  dsimp [sameJPlane]
  have h := ellFlowAction_inverse_left (-t) v.1
  exact congrArg jPlane (by simpa [neg_neg] using h)

noncomputable def ellFlowProjectiveEquiv (t : ℝ) :
    JProjectiveState ≃ JProjectiveState where
  toFun := ellFlowProjectiveAction t
  invFun := ellFlowProjectiveAction (-t)
  left_inv := by
    intro p
    exact congrFun (ellFlowProjectiveAction_inverse_left t) p
  right_inv := by
    intro p
    exact congrFun (ellFlowProjectiveAction_inverse_right t) p

theorem ellFlowProjectiveEquiv_apply (t : ℝ)
    (v : {x : Vec4R // x ≠ 0}) :
    ellFlowProjectiveEquiv t (JProjectivize v) =
      JProjectivize ⟨ellFlowAction t v.1, ellFlowAction_ne_zero v.2⟩ := by
  rfl

theorem ellFlowProjectiveEquiv_add (s t : ℝ) :
    ellFlowProjectiveEquiv (s + t) =
      (ellFlowProjectiveEquiv t).trans (ellFlowProjectiveEquiv s) := by
  apply Equiv.ext
  intro p
  exact congrFun (ellFlowProjectiveAction_add s t) p

theorem ellFlowProjectiveEquiv_zero :
    ellFlowProjectiveEquiv 0 = Equiv.refl JProjectiveState := by
  apply Equiv.ext
  intro p
  exact congrFun ellFlowProjectiveAction_zero p

theorem ellFlowProjectiveEquiv_symm (t : ℝ) :
    (ellFlowProjectiveEquiv t).symm = ellFlowProjectiveEquiv (-t) := by
  apply Equiv.ext
  intro p
  rfl

end InfoGeometry.Projective.SplitQuaternionRankOneKreinProjective
