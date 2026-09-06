import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic
import InfoGeometry.Architecture.CartanLieBracket

noncomputable section

namespace InfoGeometry.Architecture.CartanSectional

open InfoGeometry.Architecture

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Nomizu Riemann curvature tensor: R(X, Y)Z = -[[X, Y], Z]. -/
def riemannCurvature (bracket : V → V → V) (X Y Z : V) : V :=
  - bracket (bracket X Y) Z

/-- Invariant bilinear form on the Lie algebra. -/
structure InvariantBilin (bracket : V → V → V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop where
  symm : ∀ x y, B x y = B y x
  ad_invariant : ∀ x y z, B (bracket x y) z + B y (bracket x z) = 0

/-- Unnormalized sectional curvature numerator: K_num(X, Y) = B(R(X, Y)Y, X). -/
def sectionalNumerator (bracket : V → V → V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (X Y : V) : ℝ :=
  B (riemannCurvature bracket X Y Y) X

/-- 
  THEOREM 1: The curvature inner product satisfies:
  B(R(X, Y)Y, X) = B([X, Y], [X, Y]).
-/
theorem sectional_numerator_eq_bracket_sq
    (bracket : V → V → V) (h_lie : IsLieBracket bracket)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : InvariantBilin bracket B)
    (X Y : V) :
    sectionalNumerator bracket B X Y = B (bracket X Y) (bracket X Y) := by
  dsimp [sectionalNumerator, riemannCurvature]
  rw [LinearMap.map_neg, LinearMap.neg_apply]
  have h_ad := hB.ad_invariant (bracket X Y) Y X
  have h_step1 : B (bracket (bracket X Y) Y) X = - B Y (bracket (bracket X Y) X) := by
    linarith [h_ad]
  rw [h_step1, neg_neg]
  have h_skew := h_lie.skew (bracket X Y) X
  have h_step2 : bracket (bracket X Y) X = - bracket X (bracket X Y) := h_skew
  rw [h_step2, (B Y).map_neg]
  have h_symm := hB.symm Y (bracket X (bracket X Y))
  rw [h_symm]
  have h_ad2 := hB.ad_invariant X (bracket X Y) Y
  have h_step3 : B (bracket X (bracket X Y)) Y = - B (bracket X Y) (bracket X Y) := by
    linarith [h_ad2]
  rw [h_step3, neg_neg]

/-- 
  Non-compact Type Sign Theorem:
  For non-compact symmetric spaces, the Killing form on k is negative-definite:
  B(k, k) ≤ 0 for all k ∈ k.
  Therefore the sectional curvature numerator is strictly NON-POSITIVE:
    K_num(X, Y) = B([X, Y], [X, Y]) ≤ 0.
-/
theorem noncompact_curvature_nonpositive
    (bracket : V → V → V) (h_lie : IsLieBracket bracket)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : InvariantBilin bracket B)
    (k_space p_space : Submodule ℝ V)
    (h_grading : CartanGrading bracket k_space p_space)
    (h_killing_neg_on_k : ∀ k ∈ k_space, B k k ≤ 0)
    (X Y : V) (hX : X ∈ p_space) (hY : Y ∈ p_space) :
    sectionalNumerator bracket B X Y ≤ 0 := by
  rw [sectional_numerator_eq_bracket_sq bracket h_lie B hB X Y]
  have h_XY_in_k : bracket X Y ∈ k_space := h_grading.p_p X Y hX hY
  exact h_killing_neg_on_k (bracket X Y) h_XY_in_k

/-- 
  Compact Type Sign Theorem:
  For compact symmetric spaces, with positive Killing orientation on k:
  0 ≤ B(k, k) for all k ∈ k.
  Therefore the sectional curvature numerator is strictly NON-NEGATIVE:
    K_num(X, Y) = B([X, Y], [X, Y]) ≥ 0.
-/
theorem compact_curvature_nonnegative
    (bracket : V → V → V) (h_lie : IsLieBracket bracket)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : InvariantBilin bracket B)
    (k_space p_space : Submodule ℝ V)
    (h_grading : CartanGrading bracket k_space p_space)
    (h_killing_pos_on_k : ∀ k ∈ k_space, 0 ≤ B k k)
    (X Y : V) (hX : X ∈ p_space) (hY : Y ∈ p_space) :
    0 ≤ sectionalNumerator bracket B X Y := by
  rw [sectional_numerator_eq_bracket_sq bracket h_lie B hB X Y]
  have h_XY_in_k : bracket X Y ∈ k_space := h_grading.p_p X Y hX hY
  exact h_killing_pos_on_k (bracket X Y) h_XY_in_k

end InfoGeometry.Architecture.CartanSectional

end noncomputable section
