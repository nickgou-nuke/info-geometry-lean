import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.QuantumGeometry.Projective.Basic
import InfoGeometry.QuantumGeometry.Projective.QGT

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective

open scoped InnerProductSpace
open ContinuousLinearMap

/-- A Krein space structure on a Hilbert space V witnessed by a fundamental symmetry J. -/
structure KreinSpace (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] where
  J : V →L[ℂ] V
  J_involutive : J.comp J = ContinuousLinearMap.id ℂ V
  J_selfAdjoint : ContinuousLinearMap.adjoint J = J

namespace KreinSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (K : KreinSpace V)

/-- The indefinite Krein sesquilinear form η(x, y) = ⟪J x, y⟫_H. -/
def form (x y : V) : ℂ :=
  inner (𝕜 := ℂ) (K.J x) y

/-- Predicate for an operator being skew-adjoint with respect to the Krein form η. -/
def IsKreinSkewAdjoint (A : V →L[ℂ] V) : Prop :=
  ∀ x y : V, K.form (A x) y = - K.form x (A y)

theorem form_symm_J (x y : V) :
    inner (𝕜 := ℂ) (K.J x) y = inner (𝕜 := ℂ) x (K.J y) := by
  have h := adjoint_inner_right K.J x y
  rw [K.J_selfAdjoint] at h
  exact h.symm

/-- 
  Characterization: A is Krein-skew-adjoint iff J ∘ A is Hilbert-skew-adjoint.
-/
theorem isKreinSkewAdjoint_iff (A : V →L[ℂ] V) :
    K.IsKreinSkewAdjoint A ↔ ContinuousLinearMap.adjoint (K.J.comp A) = -(K.J.comp A) := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.neg_apply, inner_neg_right]
    have h_adj := adjoint_inner_right (K.J.comp A) y x
    dsimp [ContinuousLinearMap.comp_apply] at h_adj
    rw [h_adj]
    have h_form := h y x
    dsimp [form] at h_form
    rw [h_form]
    have hJ := form_symm_J K y (A x)
    rw [hJ]
    rfl
  · intro h x y
    dsimp [form]
    have h_adj : inner (𝕜 := ℂ) (K.J (A x)) y = inner (𝕜 := ℂ) x ((ContinuousLinearMap.adjoint (K.J.comp A)) y) := by
      have h1 := (adjoint_inner_right (K.J.comp A) x y).symm
      simpa [ContinuousLinearMap.comp_apply] using h1
    rw [h_adj, h]
    rw [ContinuousLinearMap.neg_apply, inner_neg_right]
    have hJ := form_symm_J K x (A y)
    rw [hJ]
    change -⟪x, K.J (A y)⟫_ℂ = -⟪x, K.J (A y)⟫_ℂ
    rfl

/-- Positive fundamental projector P₊ = (1 + J) / 2. -/
def projPlus : V →L[ℂ] V :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ V + K.J)

/-- Negative fundamental projector P₋ = (1 - J) / 2. -/
def projMinus : V →L[ℂ] V :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ V - K.J)

@[simp]
theorem projPlus_add_projMinus :
    K.projPlus + K.projMinus = ContinuousLinearMap.id ℂ V := by
  dsimp [projPlus, projMinus]
  ext x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.sub_apply]
  have h_half : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  calc
    (1 / 2 : ℂ) • (x + K.J x) + (1 / 2 : ℂ) • (x - K.J x)
        = ((1 / 2 : ℂ) • x + (1 / 2 : ℂ) • K.J x) + ((1 / 2 : ℂ) • x - (1 / 2 : ℂ) • K.J x) := by
            rw [smul_add, smul_sub]
    _ = (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • x := by abel
    _ = (1 / 2 + 1 / 2 : ℂ) • x := (add_smul _ _ x).symm
    _ = (1 : ℂ) • x := by rw [h_half]
    _ = x := one_smul ℂ x

@[simp]
theorem projPlus_idempotent :
    K.projPlus.comp K.projPlus = K.projPlus := by
  dsimp [projPlus]
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply]
  have hJ2 : K.J (K.J x) = x := by
    have h := congrArg (fun T : V →L[ℂ] V => T x) K.J_involutive
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have h_half : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  calc
    (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x + K.J x) + K.J ((1 / 2 : ℂ) • (x + K.J x)))
        = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x + K.J x) + (1 / 2 : ℂ) • (K.J x + x)) := by
            rw [map_smul, map_add, hJ2]
    _ = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x + K.J x) + (1 / 2 : ℂ) • (x + K.J x)) := by
            rw [add_comm (K.J x) x]
    _ = (1 / 2 : ℂ) • ((1 / 2 + 1 / 2 : ℂ) • (x + K.J x)) := by rw [add_smul]
    _ = (1 / 2 : ℂ) • ((1 : ℂ) • (x + K.J x)) := by rw [h_half]
    _ = (1 / 2 : ℂ) • (x + K.J x) := by rw [one_smul]

@[simp]
theorem projMinus_idempotent :
    K.projMinus.comp K.projMinus = K.projMinus := by
  dsimp [projMinus]
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hJ2 : K.J (K.J x) = x := by
    have h := congrArg (fun T : V →L[ℂ] V => T x) K.J_involutive
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have h_half : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  calc
    (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x - K.J x) - K.J ((1 / 2 : ℂ) • (x - K.J x)))
        = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x - K.J x) - (1 / 2 : ℂ) • (K.J x - x)) := by
            rw [map_smul, map_sub, hJ2]
    _ = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x - K.J x) + (1 / 2 : ℂ) • (x - K.J x)) := by
            have h_neg : -((1 / 2 : ℂ) • (K.J x - x)) = (1 / 2 : ℂ) • (x - K.J x) := by
              rw [← smul_neg, neg_sub]
            rw [sub_eq_add_neg, h_neg]
    _ = (1 / 2 : ℂ) • ((1 / 2 + 1 / 2 : ℂ) • (x - K.J x)) := by rw [add_smul]
    _ = (1 / 2 : ℂ) • ((1 : ℂ) • (x - K.J x)) := by rw [h_half]
    _ = (1 / 2 : ℂ) • (x - K.J x) := by rw [one_smul]

@[simp]
theorem projPlus_comp_projMinus :
    K.projPlus.comp K.projMinus = 0 := by
  dsimp [projPlus, projMinus]
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  have hJ2 : K.J (K.J x) = x := by
    have h := congrArg (fun T : V →L[ℂ] V => T x) K.J_involutive
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  calc
    (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x - K.J x) + K.J ((1 / 2 : ℂ) • (x - K.J x)))
        = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x - K.J x) + (1 / 2 : ℂ) • (K.J x - x)) := by
            rw [map_smul, map_sub, hJ2]
    _ = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (x - K.J x) - (1 / 2 : ℂ) • (x - K.J x)) := by
            have h_neg : (1 / 2 : ℂ) • (K.J x - x) = -((1 / 2 : ℂ) • (x - K.J x)) := by
              rw [← smul_neg, neg_sub]
            rw [h_neg, ← sub_eq_add_neg]
    _ = (1 / 2 : ℂ) • 0 := by rw [sub_self]
    _ = 0 := smul_zero _

/-- On the positive eigenspace J x = x, the Krein form matches the Hilbert inner product. -/
theorem form_eq_inner_on_plus {x y : V} (hx : K.J x = x) :
    K.form x y = inner (𝕜 := ℂ) x y := by
  dsimp [form]
  rw [hx]

/-- On a positive eigenstate J ψ = ψ, the Krein norm matches the Hilbert norm. -/
theorem form_self_eq_normSq_on_plus {x : V} (hx : K.J x = x) :
    (K.form x x).re = ‖x‖ ^ 2 := by
  rw [form_eq_inner_on_plus K hx]
  have h_norm := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  rw [h_norm]
  change (Complex.ofReal (‖x‖) ^ 2).re = ‖x‖ ^ 2
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re (‖x‖ ^ 2)

end KreinSpace

end InfoGeometry.QuantumGeometry.Projective

end noncomputable section
