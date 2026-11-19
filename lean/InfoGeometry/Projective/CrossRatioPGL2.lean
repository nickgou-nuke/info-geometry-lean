/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace InfoGeometry.Projective.CrossRatioPGL2

open Complex Matrix

noncomputable section

/-- Non-commutativity ground theorem on `2 × 2` spin matrices over `ℂ`. -/
theorem crossRatioPGL2_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Homogeneous coordinates for a point on ℂP¹ as a pair (Z₀, Z₁). -/
def ProjPoint := ℂ × ℂ

/-- The determinant bracket ⟨P, Q⟩ = P₀ * Q₁ - P₁ * Q₀. -/
def detBracket (P Q : ProjPoint) : ℂ :=
  P.1 * Q.2 - P.2 * Q.1

/-- Action of a 2×2 matrix M on a projective point P: MP = (M₀₀ P₀ + M₀₁ P₁, M₁₀ P₀ + M₁₁ P₁). -/
def matrixAct (M : Matrix (Fin 2) (Fin 2) ℂ) (P : ProjPoint) : ProjPoint :=
  (M 0 0 * P.1 + M 0 1 * P.2, M 1 0 * P.1 + M 1 1 * P.2)

/-- The projective cross-ratio [P₁, P₂; P₃, P₄] = (⟨P₁, P₂⟩ * ⟨P₃, P₄⟩) / (⟨P₁, P₃⟩ * ⟨P₂, P₄⟩). -/
def crossRatio (P1 P2 P3 P4 : ProjPoint) : ℂ :=
  (detBracket P1 P2 * detBracket P3 P4) / (detBracket P1 P3 * detBracket P2 P4)

/-- Affine embedding s ↦ [s : 1]. -/
def affinePoint (s : ℂ) : ProjPoint :=
  (s, 1)

/-- The point at infinity [1 : 0]. -/
def pointAtInfinity : ProjPoint :=
  (1, 0)

/-- The zero focus z₀ = 3/2. -/
def z0 : ℂ := ⟨3 / 2, 0⟩

/-- The pole focus p₀ = -1/2. -/
def p0 : ℂ := ⟨-1 / 2, 0⟩

/-!
### 1. Determinant Bracket Properties
-/

/-- 🏆 THEOREM 1: The determinant bracket between affine points is ⟨[s₁ : 1], [s₂ : 1]⟩ = s₁ - s₂. -/
theorem detBracket_affine (s1 s2 : ℂ) :
    detBracket (affinePoint s1) (affinePoint s2) = s1 - s2 := by
  unfold detBracket affinePoint
  dsimp
  ring

/-- 🏆 THEOREM 2: The determinant bracket with the point at infinity is ⟨[s : 1], [1 : 0]⟩ = -1. -/
theorem detBracket_infinity (s : ℂ) :
    detBracket (affinePoint s) pointAtInfinity = -1 := by
  unfold detBracket affinePoint pointAtInfinity
  dsimp
  ring

/-- 🏆 THEOREM 3: Matrix action scales the determinant bracket by det M: ⟨MP, MQ⟩ = (det M) * ⟨P, Q⟩. -/
theorem detBracket_matrix_action (M : Matrix (Fin 2) (Fin 2) ℂ) (P Q : ProjPoint) :
    detBracket (matrixAct M P) (matrixAct M Q) = M.det * detBracket P Q := by
  unfold detBracket matrixAct
  rw [Matrix.det_fin_two]
  dsimp
  ring

/-!
### 2. PGL(2, ℂ) Invariance of the Cross-Ratio
-/

private theorem crossRatio_mul_cancel (d a b c e : ℂ) (hd : d ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) :
    ((d * a) * (d * b)) / ((d * c) * (d * e)) = (a * b) / (c * e) := by
  have hden1 : (d * c) * (d * e) ≠ 0 := mul_ne_zero (mul_ne_zero hd hc) (mul_ne_zero hd he)
  have hden2 : c * e ≠ 0 := mul_ne_zero hc he
  exact (div_eq_div_iff hden1 hden2).mpr (by ring)

/-- 🏆 THEOREM 4: The cross-ratio is strictly invariant under invertible 2×2 projective transformations. -/
theorem cross_ratio_pgl2_invariant
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0)
    (P1 P2 P3 P4 : ProjPoint)
    (h_denom : detBracket P1 P3 ≠ 0 ∧ detBracket P2 P4 ≠ 0) :
    crossRatio (matrixAct M P1) (matrixAct M P2) (matrixAct M P3) (matrixAct M P4) =
    crossRatio P1 P2 P3 P4 := by
  unfold crossRatio
  rw [detBracket_matrix_action M P1 P2,
      detBracket_matrix_action M P3 P4,
      detBracket_matrix_action M P1 P3,
      detBracket_matrix_action M P2 P4]
  exact crossRatio_mul_cancel M.det (detBracket P1 P2) (detBracket P3 P4)
    (detBracket P1 P3) (detBracket P2 P4) hM h_denom.1 h_denom.2

/-!
### 3. Reduction to the Apollonian Möbius Map
-/

/-- 🏆 THEOREM 5: The cross-ratio [s, z₀; p₀, ∞] equals identically the Apollonian map w(s) = (s - z₀) / (s - p₀). -/
theorem apollonian_cross_ratio_eq_moebius (s : ℂ) (hs : s - p0 ≠ 0) :
    crossRatio (affinePoint s) (affinePoint z0) (affinePoint p0) pointAtInfinity =
    (s - z0) / (s - p0) := by
  unfold crossRatio
  rw [detBracket_affine s z0,
      detBracket_affine s p0,
      detBracket_infinity p0,
      detBracket_infinity z0]
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  exact (div_eq_div_iff (mul_ne_zero hs hm1) hs).mpr (by ring)

/-! The reusable boundary is given by the individual projective identities
    above; the former aggregate synthesis theorem is omitted. -/

end
end InfoGeometry.Projective.CrossRatioPGL2
