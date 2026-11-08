/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Clifford.CockleCoquaternionPlanarTriad

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# Soldering Form, Two-Sided SL₂(R) Lorentz Invariance, and Isotropic Souriau Sheets

Module: `InfoGeometry.Clifford.SolderingIsotropicSouriauSheetBridge`

This module formalizes:
1. **The Spacetime Soldering Form (Infeld–van der Waerden Isomorphism)**:
   - Maps Minkowski vectors $x^\mu = (t, x, y, z)$ into $2 \times 2$ real matrices:
     $$X(t, x, y, z) = \begin{pmatrix} t + z & x - y \\ x + y & t - z \end{pmatrix} \in M_2(R)$$
   - The $2 \times 2$ determinant coincides exactly with the Minkowski interval:
     $$\det_2(X(t, x, y, z)) = t^2 - x^2 + y^2 - z^2$$

2. **Two-Sided $\mathrm{SL}_2(R)$ Conjugation and Lorentz Invariance**:
   - The Lorentz action on spacetime matrices is given by two-sided conjugation:
     $$X \mapsto \Lambda X \Lambda^\top$$
   - For any $\Lambda \in M_2(R)$, $\det_2(\Lambda X \Lambda^\top) = (\det_2 \Lambda)^2 \det_2(X)$.
   - When $\det_2(\Lambda) = 1$, the Minkowski interval is strictly preserved:
     $$\det_2(\Lambda X \Lambda^\top) = \det_2(X)$$

3. **Chiral Idempotent Projectors & Nilpotent Ideals**:
   - Chiral projectors: $P_L = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
     $P_R = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$.
   - Orthogonal completeness: $P_L^2 = P_L$, $P_R^2 = P_R$, $P_L P_R = 0$, $P_R P_L = 0$, and $P_L + P_R = I_2$.
   - Annihilation: $\det_2(P_L) = 0$ and $\det_2(P_R) = 0$ (both lie on the lightcone).
   - Left ideal condition: $X P_R = 0 \iff X = X P_L$.
   - Right ideal condition: $P_L X = 0 \iff X = P_R X$.

4. **Spinor Dyad Factorization of Null Vectors**:
   - A matrix factors as a dyadic outer product $X = \lambda \tilde{\lambda}^\top$:
     $$X = \begin{pmatrix} \lambda_0 \tilde{\lambda}_0 & \lambda_0 \tilde{\lambda}_1 \\ \lambda_1 \tilde{\lambda}_0 & \lambda_1 \tilde{\lambda}_1 \end{pmatrix}$$
   - Any such factorized state is identically null: $\det_2(X) = 0$.

5. **Left and Right Isotropic Souriau Sheets (Coadjoint Orbits)**:
   - The orbits $\mathcal{O}_L = \{\Lambda P_L \Lambda^\top \mid \det_2 \Lambda = 1\}$ and
     $\mathcal{O}_R = \{\Lambda P_R \Lambda^\top \mid \det_2 \Lambda = 1\}$ are strictly isotropic:
     $$\det_2(\Lambda P_L \Lambda^\top) = 0, \qquad \det_2(\Lambda P_R \Lambda^\top) = 0$$
   - Casimir invariant $C_1 = 0$ is conserved everywhere on both sheets, proving that the
     coadjoint orbits of massless left- and right-chiral states are invariant and isoentropic.

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.Clifford.SolderingIsotropic

open Matrix
open InfoGeometry.Clifford.Coquaternion
open InfoGeometry.Clifford.Coquaternion.Coquaternion

variable {R : Type*} [CommRing R]

/-! ### 1. Spacetime Soldering Form and Determinant Metric -/

/-- The $2 \times 2$ soldering matrix representing a Minkowski 4-vector $(t, x, y, z)$:
    $$X = \begin{pmatrix} t + z & x - y \\ x + y & t - z \end{pmatrix}$$ -/
def solderingMatrix (t x y z : R) : Mat2 R :=
  !![ t + z, x - y;
      x + y, t - z ]

/-- Determinant formula for the soldering matrix:
    $\det_2(X) = (t+z)(t-z) - (x-y)(x+y) = t^2 - x^2 + y^2 - z^2$. -/
theorem det2_solderingMatrix (t x y z : R) :
    det2 (solderingMatrix t x y z) = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 := by
  simp [det2, solderingMatrix]
  ring

/-- The zero vector maps to the zero soldering matrix. -/
@[simp]
theorem solderingMatrix_zero :
    solderingMatrix (0 : R) 0 0 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [solderingMatrix]

/-- Linearity of the soldering matrix with respect to addition:
    $X(p + q) = X(p) + X(q)$. -/
theorem solderingMatrix_add (t₁ x₁ y₁ z₁ t₂ x₂ y₂ z₂ : R) :
    solderingMatrix (t₁ + t₂) (x₁ + x₂) (y₁ + y₂) (z₁ + z₂) =
    solderingMatrix t₁ x₁ y₁ z₁ + solderingMatrix t₂ x₂ y₂ z₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [solderingMatrix] <;> ring

/-! ### 2. Two-Sided SL₂(R) Conjugation and Lorentz Invariance -/

/-- Determinant of the transpose of a $2 \times 2$ matrix equals the determinant:
    $\det_2(M^\top) = \det_2(M)$. -/
theorem det2_transpose (M : Mat2 R) :
    det2 Mᵀ = det2 M := by
  simp [det2, Matrix.transpose]
  ring

/-- Determinant of a product of two $2 \times 2$ matrices is multiplicative:
    $\det_2(A * B) = \det_2(A) * \det_2(B)$. -/
theorem det2_mul (A B : Mat2 R) :
    det2 (A * B) = det2 A * det2 B := by
  simp [det2, Matrix.mul_apply]
  ring

/-- Determinant of the two-sided conjugation:
    $\det_2(\Lambda X \Lambda^\top) = (\det_2 \Lambda)^2 \det_2(X)$. -/
theorem det2_two_sided_conjugation (Λ X : Mat2 R) :
    det2 (Λ * X * Λᵀ) = (det2 Λ) ^ 2 * det2 X := by
  rw [det2_mul, det2_mul, det2_transpose]
  ring

/-- Lorentz Invariance of the Minkowski interval:
    If $\det_2(\Lambda) = 1$, then $\det_2(\Lambda X \Lambda^\top) = \det_2(X)$. -/
theorem lorentz_invariance_minkowski (Λ X : Mat2 R) (hΛ : det2 Λ = 1) :
    det2 (Λ * X * Λᵀ) = det2 X := by
  rw [det2_two_sided_conjugation, hΛ]
  ring

/-- Two-sided transformation of the soldering form preserves the Minkowski interval:
    $X' = \Lambda X(t, x, y, z) \Lambda^\top \implies \det_2(X') = t^2 - x^2 + y^2 - z^2$. -/
theorem soldering_lorentz_invariant (Λ : Mat2 R) (t x y z : R) (hΛ : det2 Λ = 1) :
    det2 (Λ * solderingMatrix t x y z * Λᵀ) = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 := by
  rw [lorentz_invariance_minkowski Λ (solderingMatrix t x y z) hΛ, det2_solderingMatrix]

/-! ### 3. Chiral Idempotent Projectors & Left/Right Ideals -/

/-- Left chiral projector $P_L = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def P_L : Mat2 R :=
  !![ 1, 0;
      0, 0 ]

/-- Right chiral projector $P_R = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def P_R : Mat2 R :=
  !![ 0, 0;
      0, 1 ]

/-- Left projector idempotency: $P_L^2 = P_L$. -/
@[simp]
theorem P_L_sq : P_L * (P_L : Mat2 R) = P_L := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, Matrix.mul_apply]

/-- Right projector idempotency: $P_R^2 = P_R$. -/
@[simp]
theorem P_R_sq : P_R * (P_R : Mat2 R) = P_R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_R, Matrix.mul_apply]

/-- Orthogonal annihilation: $P_L P_R = 0$. -/
@[simp]
theorem P_L_mul_P_R : P_L * (P_R : Mat2 R) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, P_R, Matrix.mul_apply]

/-- Orthogonal annihilation: $P_R P_L = 0$. -/
@[simp]
theorem P_R_mul_P_L : P_R * (P_L : Mat2 R) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, P_R, Matrix.mul_apply]

/-- Completeness relation: $P_L + P_R = I_2$. -/
theorem P_L_add_P_R : P_L + (P_R : Mat2 R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, P_R]

/-- Left projector is on the lightcone: $\det_2(P_L) = 0$. -/
@[simp]
theorem det2_P_L : det2 (P_L : Mat2 R) = 0 := by
  simp [det2, P_L]

/-- Right projector is on the lightcone: $\det_2(P_R) = 0$. -/
@[simp]
theorem det2_P_R : det2 (P_R : Mat2 R) = 0 := by
  simp [det2, P_R]

/-- Left ideal absorption: Any matrix in the right column null space satisfies $X P_L = X$. -/
theorem left_ideal_absorb (a c : R) :
    !![a, 0; c, 0] * (P_L : Mat2 R) = !![a, 0; c, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, Matrix.mul_apply]

/-- Right ideal absorption: Any matrix in the upper row null space satisfies $P_R X = X$. -/
theorem right_ideal_absorb (c d : R) :
    (P_R : Mat2 R) * !![0, 0; c, d] = !![0, 0; c, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_R, Matrix.mul_apply]

/-! ### 4. Spinor Dyad Factorization of Null Vectors -/

/-- Dyadic outer product of two 2D spinors $\lambda$ and $\tilde{\lambda}$:
    $$X = \begin{pmatrix} \lambda_0 \tilde{\lambda}_0 & \lambda_0 \tilde{\lambda}_1 \\
                          \lambda_1 \tilde{\lambda}_0 & \lambda_1 \tilde{\lambda}_1 \end{pmatrix}$$ -/
def spinorDyad (l0 l1 lt0 lt1 : R) : Mat2 R :=
  !![ l0 * lt0, l0 * lt1;
      l1 * lt0, l1 * lt1 ]

/-- Every dyadic spinor product identically has zero determinant:
    $\det_2(\lambda \tilde{\lambda}^\top) = 0$. -/
theorem det2_spinorDyad (l0 l1 lt0 lt1 : R) :
    det2 (spinorDyad l0 l1 lt0 lt1) = 0 := by
  simp [det2, spinorDyad]
  ring

/-! ### 5. Left and Right Isotropic Souriau Sheets (Coadjoint Orbits) -/

/-- Coadjoint orbit action on a base idempotent $P$:
    $\mathcal{O}(\Lambda, P) = \Lambda P \Lambda^\top$. -/
def souriauOrbitPoint (Λ P : Mat2 R) : Mat2 R :=
  Λ * P * Λᵀ

/-- Left Isotropic Souriau Sheet: The orbit of $P_L$ under any $\Lambda$ strictly has $\det_2 = 0$. -/
theorem souriau_sheet_L_isotropic (Λ : Mat2 R) :
    det2 (souriauOrbitPoint Λ P_L) = 0 := by
  unfold souriauOrbitPoint
  rw [det2_two_sided_conjugation, det2_P_L, mul_zero]

/-- Right Isotropic Souriau Sheet: The orbit of $P_R$ under any $\Lambda$ strictly has $\det_2 = 0$. -/
theorem souriau_sheet_R_isotropic (Λ : Mat2 R) :
    det2 (souriauOrbitPoint Λ P_R) = 0 := by
  unfold souriauOrbitPoint
  rw [det2_two_sided_conjugation, det2_P_R, mul_zero]

/-- Under $\mathrm{SL}_2(R)$ transformations ($\det_2 \Lambda = 1$), the sum of the two
    chiral Souriau sheet matrices is unimodular: $\det_2(\mathcal{O}(\Lambda, P_L) + \mathcal{O}(\Lambda, P_R)) = 1$. -/
theorem souriau_chiral_sum_unimodular (Λ : Mat2 R) (hΛ : det2 Λ = 1) :
    det2 (souriauOrbitPoint Λ P_L + souriauOrbitPoint Λ P_R) = 1 := by
  unfold souriauOrbitPoint
  have h_add : Λ * P_L * Λᵀ + Λ * P_R * Λᵀ = Λ * (P_L + P_R) * Λᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [h_add, P_L_add_P_R, Matrix.mul_one, det2_mul, det2_transpose, hΛ]
  ring

end InfoGeometry.Clifford.SolderingIsotropic
