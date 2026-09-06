import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Krein.HilbertBridge

This module establishes the 45-degree rotation bridge between the
diagonal `DoubledSpace` (Pontryagin model) and the `NeutralSpace` (Bogoliubov model).

It provides the equivariant chart for the modular flow, ensuring that
evolutionary parameters of Cartan generators are correctly transported
between the state space representations.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- NeutralSpace — Hessian / Bogoliubov neutral Krein model.
Wrapped to prevent instance resonance with the diagonal/DoubledSpace model. -/
structure NeutralSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  val : WithLp (2 : ENNReal) (E × E)

namespace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[ext] lemma ext {u v : NeutralSpace E} (h : u.val = v.val) : u = v := by
  cases u; cases v; cases h; rfl

instance : NormedAddCommGroup (NeutralSpace E) where
  norm u := ‖u.val‖
  dist u v := dist u.val v.val
  edist u v := edist u.val v.val
  dist_eq := fun u v => dist_eq_norm u.val v.val
  dist_self := fun u => dist_self u.val
  dist_comm := fun u v => dist_comm u.val v.val
  dist_triangle := fun u v w => dist_triangle u.val v.val w.val
  eq_of_dist_eq_zero := fun {u v} h => ext (eq_of_dist_eq_zero h)

instance : InnerProductSpace ℝ (NeutralSpace E) where
  inner u v := ⟪u.val, v.val⟫_ℝ
  norm_sq_eq_re_inner u := norm_sq_eq_re_inner u.val
  conj_inner_symm u v := real_inner_comm u.val v.val
  add_left u v w := inner_add_left
  smul_left r u v := real_inner_smul_left

/-- The swap `J(x,y) = (y,x)` as the fundamental symmetry of the neutral model. -/
noncomputable def neutralJ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃ₗᵢ[ℝ] NeutralSpace E where
  toFun u := ⟨WithLp.toLp 2 ((WithLp.ofLp u.val).2, (WithLp.ofLp u.val).1)⟩
  invFun u := ⟨WithLp.toLp 2 ((WithLp.ofLp u.val).2, (WithLp.ofLp u.val).1)⟩
  left_inv u := by rcases u with ⟨v⟩; rcases v with ⟨x, ξ⟩; simp
  right_inv u := by rcases u with ⟨v⟩; rcases v with ⟨x, ξ⟩; simp
  map_add' u v := by
    apply ext; apply (WithLp.ofLp_injective 2)
    rcases u with ⟨u_val⟩; rcases v with ⟨v_val⟩
    rcases u_val with ⟨x, ξ⟩; rcases v_val with ⟨y, η⟩
    simp
  map_smul' r u := by
    apply ext; apply (WithLp.ofLp_injective 2)
    rcases u with ⟨u_val⟩; rcases u_val with ⟨x, ξ⟩
    simp
  norm_map' u := by
    rcases u with ⟨u_val⟩; rcases u_val with ⟨x, ξ⟩
    simp only [WithLp.prod_norm_sq_eq_of_L2, add_comm]

instance : KreinSpace (NeutralSpace E) where
  J := neutralJ E
  J_invol u := by rcases u with ⟨v⟩; rcases v with ⟨x, ξ⟩; simp [neutralJ]
  J_selfAdj u v := by
    rcases u with ⟨u_val⟩; rcases v with ⟨v_val⟩
    rcases u_val with ⟨x, ξ⟩; rcases v_val with ⟨y, η⟩
    simp [neutralJ, WithLp.prod_inner_apply, add_comm]

/-! ### The 45-degree Bridge Isometry -/

lemma inv_sqrt_two_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  rw [one_div_pow, Real.sq_sqrt]
  norm_num

/-- The 45-degree isometry `D(x, ξ) ↦ ((x+ξ)/√2, (x-ξ)/√2)`.
Acts as the equivariant chart mapping the diagonal state space (Pontryagin)
to the neutral Hessian space (Bogoliubov). -/
noncomputable def rotation45 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗᵢ[ℝ] NeutralSpace E where
  toFun u := ⟨WithLp.toLp 2 (
    (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp u).1 + (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp u).2,
    (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp u).1 - (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp u).2)⟩
  invFun v := WithLp.toLp 2 (
    (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp v.val).1 + (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp v.val).2,
    (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp v.val).1 - (1/Real.sqrt 2 : ℝ) • (WithLp.ofLp v.val).2)
  left_inv u := by
    apply (WithLp.ofLp_injective 2)
    rcases u with ⟨x, ξ⟩
    simp only [WithLp.ofLp_toLp]
    have hsq := inv_sqrt_two_sq
    ext
    · simp only [smul_add, smul_sub, smul_smul, ← add_smul, ← sub_smul]
      rw [hsq]; simp; ring
    · simp only [smul_add, smul_sub, smul_smul, ← add_smul, ← sub_smul]
      rw [hsq]; simp; ring
  right_inv v := by
    apply ext
    apply (WithLp.ofLp_injective 2)
    rcases v with ⟨v_val⟩
    rcases v_val with ⟨x, ξ⟩
    simp only [WithLp.ofLp_toLp]
    have hsq := inv_sqrt_two_sq
    ext
    · simp only [smul_add, smul_sub, smul_smul, ← add_smul, ← sub_smul]
      rw [hsq]; simp; ring
    · simp only [smul_add, smul_sub, smul_smul, ← add_smul, ← sub_smul]
      rw [hsq]; simp; ring
  map_add' u v := by
    apply ext; apply (WithLp.ofLp_injective 2)
    rcases u with ⟨x, ξ⟩; rcases v with ⟨y, η⟩
    simp only [WithLp.ofLp_add, WithLp.ofLp_toLp, smul_add]
    ext <;> simp <;> ring
  map_smul' r u := by
    apply ext; apply (WithLp.ofLp_injective 2)
    rcases u with ⟨x, ξ⟩
    simp only [WithLp.ofLp_smul, WithLp.ofLp_toLp, smul_add, smul_sub, smul_smul]
    ext <;> simp <;> ring
  norm_map' u := by
    rcases u with ⟨x, ξ⟩
    simp only [WithLp.prod_norm_sq_eq_of_L2]
    have hsq := inv_sqrt_two_sq
    calc
      ‖(1 / √2 : ℝ) • x + (1 / √2 : ℝ) • ξ‖ ^ 2 + ‖(1 / √2 : ℝ) • x - (1 / √2 : ℝ) • ξ‖ ^ 2
          = (1 / √2 : ℝ) ^ 2 * ‖x + ξ‖ ^ 2 + (1 / √2 : ℝ) ^ 2 * ‖x - ξ‖ ^ 2 := by
            simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            rfl
      _ = (1 / 2 : ℝ) * (‖x + ξ‖ ^ 2 + ‖x - ξ‖ ^ 2) := by rw [hsq, mul_add]
      _ = (1 / 2 : ℝ) * (2 * (‖x‖ ^ 2 + ‖ξ‖ ^ 2)) := by rw [norm_add_pow_two_add_norm_sub_pow_two]
      _ = ‖x‖ ^ 2 + ‖ξ‖ ^ 2 := by ring

/-- The chart lift of an operator (e.g. Cartan generator) from DoubledSpace to NeutralSpace. -/
noncomputable def neutralLift (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E where
  toFun u := (rotation45 E).toFun (A ((rotation45 E).invFun u))
  map_add' u v := by
    apply NeutralSpace.ext
    simp [rotation45, map_add]
  map_smul' r u := by
    apply NeutralSpace.ext
    simp [rotation45, map_smul]

end NeutralSpace

end InfoGeometry.Krein
