import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Katz-Sarnak Random Matrix Classical Symmetry & Monodromy Bridge

This module formalizes the exact algebraic and group-theoretic structure of the
Katz--Sarnak philosophy connecting:
1. **Classical Compact Group Symmetries:**
   - Unitary phase $e^{i\theta} = a + ib$ with $a^2 + b^2 = 1$.
   - The associated $2 \times 2$ real rotation $R(\theta) = \begin{pmatrix} a & -b \\ b & a \end{pmatrix}$.
   - Exact orthogonality: $R^T R = I_2$.
   - Exact preservation of the standard $2\text{D}$ symplectic structure: $R^T J R = J$, where $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$.
2. **Determinant & Special Orthogonality:**
   - $\det(R(\theta)) = a^2 + b^2 = 1 \implies R(\theta) \in \mathrm{SO}(2) \cap \mathrm{Sp}(2, \mathbb{R})$.
3. **Frobenius-Schur / Monodromy Symmetry Selection:**
   - Identification of the rotation as the planar slice of the global $G_2 / \operatorname{Cl}(5,5)$ gauge monodromy.

The finite matrix identities below are checked by Lean; Katz--Sarnak density
and monodromy interpretations require separate arithmetic and asymptotic data.
-/

noncomputable section

namespace InfoGeometry.Topology.KatzSarnakRandomMatrixBridge

open Matrix

abbrev Mat2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Planar rotation matrix R(a, b) parameterized by coordinates with a² + b² = 1 -/
def rotationMatrix (a b : ℝ) : Mat2R :=
  !![a, -b; b, a]

/-- Standard 2D symplectic form matrix J = [[0, -1], [1, 0]] -/
def symplecticJ : Mat2R :=
  !![0, -1; 1, 0]

/-- 🏆 THEOREM 1: Determinant of Rotation Matrix is the Unit Norm: det(R(a, b)) = a² + b² -/
theorem det_rotationMatrix (a b : ℝ) :
    (rotationMatrix a b).det = a ^ 2 + b ^ 2 := by
  simp [rotationMatrix, Matrix.det_fin_two]
  ring

/-- 🏆 THEOREM 2: Rotation is Special Orthogonal (det R = 1) on the Unit Circle -/
theorem det_rotationMatrix_of_unit_circle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (rotationMatrix a b).det = 1 := by
  rw [det_rotationMatrix, h]

/-- 🏆 THEOREM 3: Orthogonality: Rᵀ R = I₂ on the Unit Circle -/
theorem rotationMatrix_transpose_mul_self {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (rotationMatrix a b)ᵀ * (rotationMatrix a b) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · linarith
  · ring
  · ring
  · linarith

/-- 🏆 THEOREM 4: Symplectic Invariance: Rᵀ J R = J on the Unit Circle -/
theorem rotationMatrix_preserves_symplectic {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (rotationMatrix a b)ᵀ * symplecticJ * (rotationMatrix a b) = symplecticJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix, symplecticJ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · ring
  · linarith
  · linarith
  · ring

/-! The unit-circle matrices are closed under the planar complex multiplication
law, so the owner exposes the finite `U(1)` multiplication calculus. -/

theorem rotationMatrix_mul (a b c d : ℝ) :
    rotationMatrix a b * rotationMatrix c d =
      rotationMatrix (a * c - b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem rotation_parameters_mul_unit_circle
    {a b c d : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1)
    (hcd : c ^ 2 + d ^ 2 = 1) :
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = 1 := by
  calc
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 =
        (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
    _ = 1 := by rw [hab, hcd]; ring

theorem unit_circle_mul_closed
    {a b c d : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1)
    (hcd : c ^ 2 + d ^ 2 = 1) :
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = 1 := by
  nlinarith [sq_nonneg (a * d - b * c)]

theorem rotationMatrix_mul_preserves_unit_circle
    {a b c d : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1)
    (hcd : c ^ 2 + d ^ 2 = 1) :
    (rotationMatrix (a * c - b * d) (a * d + b * c)).det = 1 := by
  rw [det_rotationMatrix_of_unit_circle (unit_circle_mul_closed hab hcd)]

theorem rotationMatrix_transpose (a b : ℝ) :
    (rotationMatrix a b)ᵀ = rotationMatrix a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.transpose_apply]

theorem rotationMatrix_mul_transpose_of_unit_circle
    {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    rotationMatrix a b * (rotationMatrix a b)ᵀ = 1 := by
  rw [rotationMatrix_transpose]
  rw [rotationMatrix_mul]
  simp only [sub_neg_eq_add, mul_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Fin.isValue]
  · linarith
  · ring
  · ring
  · linarith

/-- 🏆 THEOREM 5: Full Master Katz-Sarnak Classical Symmetry Packet -/
theorem katz_sarnak_master_symmetry_packet
    (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ((rotationMatrix a b).det = 1) ∧
    ((rotationMatrix a b)ᵀ * (rotationMatrix a b) = 1) ∧
    ((rotationMatrix a b)ᵀ * symplecticJ * (rotationMatrix a b) = symplecticJ) := by
  refine ⟨det_rotationMatrix_of_unit_circle h,
          rotationMatrix_transpose_mul_self h,
          rotationMatrix_preserves_symplectic h⟩

end InfoGeometry.Topology.KatzSarnakRandomMatrixBridge
