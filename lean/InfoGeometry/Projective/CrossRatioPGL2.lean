/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace InfoGeometry.Projective.CrossRatioPGL2

open Complex Matrix

noncomputable section

/-!
# Projective Cross-Ratio and PGL(2, ℂ) Invariance on ℂP¹

This module formalizes the projective cross-ratio $[z_1, z_2; z_3, z_4]$ of four points
in the complex projective line $\mathbb{CP}^1$ and proves its strict algebraic invariance
under the action of the projective linear group $\mathrm{PGL}(2, \mathbb{C})$.

Key Formalized Structures:
1. **Homogeneous Coordinates**: Points $P = (u, v) \in \mathbb{C}^2 \setminus \{(0, 0)\}$.
2. **Homogeneous Determinant Bracket**:
   $$\langle P, Q \rangle = \det \begin{pmatrix} u_1 & u_2 \\ v_1 & v_2 \end{pmatrix} = u_1 v_2 - v_1 u_2$$
3. **Projective Cross-Ratio**:
   $$[P_1, P_2; P_3, P_4] = \frac{\langle P_1, P_3 \rangle \langle P_2, P_4 \rangle}{\langle P_2, P_3 \rangle \langle P_1, P_4 \rangle}$$
4. **Möbius Specialization**:
   For $P_1 = [s : 1]$, $P_2 = [z_0 : 1] = [3/2 : 1]$, $P_3 = [p_0 : 1] = [-1/2 : 1]$, $P_4 = [1 : 0] = \infty$:
   $$\mathcal{M}(s) = \frac{\langle s, z_0 \rangle \langle p_0, \infty \rangle}{\langle s, p_0 \rangle \langle z_0, \infty \rangle} = \frac{s - 3/2}{s + 1/2}$$
5. **$\mathrm{PGL}(2, \mathbb{C})$ Invariance**:
   For any matrix $M \in \mathrm{GL}(2, \mathbb{C})$:
   $$\langle M P, M Q \rangle = (\det M) \langle P, Q \rangle$$
   The determinant factors cancel out completely in the cross-ratio:
   $$[M P_1, M P_2; M P_3, M P_4] = [P_1, P_2; P_3, P_4]$$
-/

/-- Standard embedding of affine complex numbers s ∈ ℂ into ℂP¹: [s : 1]. -/
def affinePoint (s : ℂ) : ℂ × ℂ :=
  (s, 1)

/-- The point at infinity ∞ = [1 : 0] ∈ ℂP¹. -/
def pointInfinity : ℂ × ℂ :=
  (1, 0)

/-- Determinant bracket ⟨P, Q⟩ = u_P * v_Q - v_P * u_Q. -/
def detBracket (P Q : ℂ × ℂ) : ℂ :=
  P.1 * Q.2 - P.2 * Q.1

/-- Projective cross-ratio [P₁, P₂; P₃, P₄] on ℂP¹. -/
def crossRatio (P1 P2 P3 P4 : ℂ × ℂ) : ℂ :=
  (detBracket P1 P3 * detBracket P2 P4) / (detBracket P2 P3 * detBracket P1 P4)

/-- Natural Apollonian cross-ratio form:
    M(P₁, P₂, P₃, P₄) = (⟨P₁, P₂⟩ ⟨P₃, P₄⟩) / (⟨P₁, P₃⟩ ⟨P₂, P₄⟩). -/
def apollonianCrossRatio (P1 P2 P3 P4 : ℂ × ℂ) : ℂ :=
  (detBracket P1 P2 * detBracket P3 P4) / (detBracket P1 P3 * detBracket P2 P4)

/-- Action of a 2×2 matrix M on a homogeneous coordinate pair P = (u, v). -/
def matrixAction (M : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ × ℂ) : ℂ × ℂ :=
  (M 0 0 * P.1 + M 0 1 * P.2, M 1 0 * P.1 + M 1 1 * P.2)

/-!
### 1. Specialization to Affine Coordinates and the Apollonian Map
-/

/-- 🏆 THEOREM 1 (Affine Determinant Reduction):
    For affine points [s₁ : 1] and [s₂ : 1], the bracket is the affine difference:
    ⟨[s₁ : 1], [s₂ : 1]⟩ = s₁ - s₂. -/
theorem detBracket_affine (s₁ s₂ : ℂ) :
    detBracket (affinePoint s₁) (affinePoint s₂) = s₁ - s₂ := by
  unfold detBracket affinePoint
  dsimp
  ring

/-- 🏆 THEOREM 2 (Infinity Bracket Reduction):
    For affine point [s : 1] and ∞ = [1 : 0], the bracket is ⟨[s : 1], [1 : 0]⟩ = -1. -/
theorem detBracket_infinity (s : ℂ) :
    detBracket (affinePoint s) pointInfinity = -1 := by
  unfold detBracket affinePoint pointInfinity
  dsimp
  ring

/-- 🏆 THEOREM 3 (Apollonian Möbius Identification):
    The Apollonian Möbius transform w(s) = (s - 3/2)/(s + 1/2) is identically
    the projective cross-ratio with respect to zero z₀ = 3/2, pole p₀ = -1/2, and ∞:
    M([s:1], [3/2:1], [-1/2:1], [1:0]) = (s - 3/2)/(s + 1/2). -/
theorem apollonian_cross_ratio_eq_moebius (s : ℂ) :
    let z0 : ℂ := ⟨3 / 2, 0⟩
    let p0 : ℂ := ⟨-1 / 2, 0⟩
    apollonianCrossRatio (affinePoint s) (affinePoint z0) (affinePoint p0) pointInfinity =
    (s - z0) / (s - p0) := by
  intro z0 p0
  unfold apollonianCrossRatio
  rw [detBracket_affine s z0, detBracket_affine s p0,
      detBracket_infinity p0, detBracket_infinity z0]
  have h_num : (s - z0) * (-1) = - (s - z0) := by ring
  have h_den : (s - p0) * (-1) = - (s - p0) := by ring
  rw [h_num, h_den, neg_div_neg_eq]

/-!
### 2. PGL(2, ℂ) Matrix Transformation of the Determinant Bracket
-/

/-- 🏆 THEOREM 4 (Determinant Scaling of the Bracket under GL(2, ℂ)):
    For any matrix M and points P, Q ∈ ℂP¹:
    ⟨M P, M Q⟩ = (det M) * ⟨P, Q⟩. -/
theorem detBracket_matrix_action (M : Matrix (Fin 2) (Fin 2) ℂ) (P Q : ℂ × ℂ) :
    detBracket (matrixAction M P) (matrixAction M Q) = M.det * detBracket P Q := by
  unfold detBracket matrixAction
  dsimp
  rw [Matrix.det_fin_two]
  ring

/-!
### 3. PGL(2, ℂ) Invariance of the Projective Cross-Ratio
-/

/-- 🏆 THEOREM 5 (Universal PGL(2, ℂ) Invariance of the Cross-Ratio):
    The projective cross-ratio [P₁, P₂; P₃, P₄] is strictly invariant under
    any projective linear transformation M ∈ PGL(2, ℂ) with det M ≠ 0. -/
theorem cross_ratio_pgl2_invariant
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0)
    (P1 P2 P3 P4 : ℂ × ℂ) :
    crossRatio (matrixAction M P1) (matrixAction M P2) (matrixAction M P3) (matrixAction M P4) =
    crossRatio P1 P2 P3 P4 := by
  unfold crossRatio
  rw [detBracket_matrix_action M P1 P3,
      detBracket_matrix_action M P2 P4,
      detBracket_matrix_action M P2 P3,
      detBracket_matrix_action M P1 P4]
  have h_num : (M.det * detBracket P1 P3) * (M.det * detBracket P2 P4) =
               (M.det ^ 2) * (detBracket P1 P3 * detBracket P2 P4) := by ring
  have h_den : (M.det * detBracket P2 P3) * (M.det * detBracket P1 P4) =
               (M.det ^ 2) * (detBracket P2 P3 * detBracket P1 P4) := by ring
  rw [h_num, h_den]
  have h_det_sq_ne : M.det ^ 2 ≠ 0 := pow_ne_zero 2 hM
  exact mul_div_mul_left _ _ h_det_sq_ne

/-- 🏆 THEOREM 6 (PGL(2, ℂ) Invariance of the Apollonian Cross-Ratio):
    The Apollonian cross-ratio form is also strictly invariant under PGL(2, ℂ). -/
theorem apollonian_cross_ratio_pgl2_invariant
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0)
    (P1 P2 P3 P4 : ℂ × ℂ) :
    apollonianCrossRatio (matrixAction M P1) (matrixAction M P2) (matrixAction M P3) (matrixAction M P4) =
    apollonianCrossRatio P1 P2 P3 P4 := by
  unfold apollonianCrossRatio
  rw [detBracket_matrix_action M P1 P2,
      detBracket_matrix_action M P3 P4,
      detBracket_matrix_action M P1 P3,
      detBracket_matrix_action M P2 P4]
  have h_num : (M.det * detBracket P1 P2) * (M.det * detBracket P3 P4) =
               (M.det ^ 2) * (detBracket P1 P2 * detBracket P3 P4) := by ring
  have h_den : (M.det * detBracket P1 P3) * (M.det * detBracket P2 P4) =
               (M.det ^ 2) * (detBracket P1 P3 * detBracket P2 P4) := by ring
  rw [h_num, h_den]
  have h_det_sq_ne : M.det ^ 2 ≠ 0 := pow_ne_zero 2 hM
  exact mul_div_mul_left _ _ h_det_sq_ne

/-!
### 4. Grand Capstone: Projective Invariance Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Complete formal verification of the Determinant Bracket Scaling,
    Möbius identification, and PGL(2, ℂ) Cross-Ratio Invariance -/
theorem grand_cross_ratio_pgl2_synthesis
    (s : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0)
    (P1 P2 P3 P4 : ℂ × ℂ) :
    let z0 : ℂ := ⟨3 / 2, 0⟩
    let p0 : ℂ := ⟨-1 / 2, 0⟩
    (apollonianCrossRatio (affinePoint s) (affinePoint z0) (affinePoint p0) pointInfinity = (s - z0) / (s - p0)) ∧
    (detBracket (matrixAction M P1) (matrixAction M P2) = M.det * detBracket P1 P2) ∧
    (crossRatio (matrixAction M P1) (matrixAction M P2) (matrixAction M P3) (matrixAction M P4) =
     crossRatio P1 P2 P3 P4) := by
  refine ⟨apollonian_cross_ratio_eq_moebius s,
          detBracket_matrix_action M P1 P2,
          cross_ratio_pgl2_invariant M hM P1 P2 P3 P4⟩

end

end InfoGeometry.Projective.CrossRatioPGL2
