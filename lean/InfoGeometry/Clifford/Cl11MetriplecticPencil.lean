/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SignedPermutation
import InfoGeometry.OperatorAlgebra.RealMatrixSplit
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# The symmetric and skew parts of the real `Cl(1,1)` pencil

The carrier and generators are those of `Cl11Matrix`: `gen (σ, γ)` is
`σ • Eplus + γ • Eminus`, with `Eplus = diag(1,-1)` and
`Eminus = !![0,1;-1,0]`. We compute its native self-adjoint and skew-adjoint
parts and the positive sign of their ordered commutator.

The scalar multiplication pencil `σ • 1 + γ • Eminus` is a different
construction. Its product and determinant distinguish it from `gen` without
introducing complex scalars. All conclusions concern real two-by-two matrices.
No statement about zeros of a zeta function or a Weil quadratic form is made.
-/

noncomputable section

open Matrix
open scoped Matrix BigOperators

namespace InfoGeometry.Clifford.Cl11Matrix

theorem smul_Eplus_transpose (σ : ℝ) :
    (σ • Eplus)ᵀ = σ • Eplus := by
  change σ • Eplusᵀ = σ • Eplus
  rw [SignedPermutation.e1_transpose]

theorem smul_Eminus_transpose (γ : ℝ) :
    (γ • Eminus)ᵀ = -(γ • Eminus) := by
  change γ • Eminusᵀ = -(γ • Eminus)
  rw [SignedPermutation.e2_transpose, smul_neg]

/-- The native self-adjoint part is the split-signature component. -/
theorem gen_selfAdjointPart (σ γ : ℝ) :
    (selfAdjointPart ℝ (gen (σ, γ)) : Mat2) = σ • Eplus := by
  rw [InfoGeometry.OperatorAlgebra.RealMatrixSplit.selfAdjointPart_eq_half]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, Matrix.transpose_apply] <;> ring

/-- The native skew-adjoint part is the rotation component. -/
theorem gen_skewAdjointPart (σ γ : ℝ) :
    (skewAdjointPart ℝ (gen (σ, γ)) : Mat2) = γ • Eminus := by
  rw [InfoGeometry.OperatorAlgebra.RealMatrixSplit.skewAdjointPart_eq_half]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, Matrix.transpose_apply] <;> ring

/-- A skew generator has zero real quadratic form. -/
theorem smul_Eminus_quadratic (γ : ℝ) (v : Fin 2 → ℝ) :
    dotProduct v ((γ • Eminus).mulVec v) = 0 := by
  simp [Eminus, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The two coordinate directions have opposite quadratic signs. -/
theorem smul_Eplus_quadratic (σ : ℝ) (v : Fin 2 → ℝ) :
    dotProduct v ((σ • Eplus).mulVec v) = σ * (v 0 ^ 2 - v 1 ^ 2) := by
  simp [Eplus, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- This particular symmetric component is nonnegative exactly when it vanishes. -/
theorem smul_Eplus_quadratic_nonneg_iff (σ : ℝ) :
    (∀ v : Fin 2 → ℝ, 0 ≤ dotProduct v ((σ • Eplus).mulVec v)) ↔ σ = 0 := by
  constructor
  · intro h
    have h₀ := h ![1, 0]
    have h₁ := h ![0, 1]
    rw [smul_Eplus_quadratic] at h₀ h₁
    norm_num at h₀ h₁
    linarith
  · rintro rfl v
    simp

/-- The quadratic criterion is exactly Mathlib's positive semidefinite predicate. -/
theorem smul_Eplus_posSemidef_iff (σ : ℝ) :
    (σ • Eplus).PosSemidef ↔ σ = 0 := by
  constructor
  · intro h
    apply (smul_Eplus_quadratic_nonneg_iff σ).mp
    intro v
    simpa using h.dotProduct_mulVec_nonneg v
  · rintro rfl
    simpa using (Matrix.PosSemidef.zero : (0 : Mat2).PosSemidef)

/-- Every nonzero split-signature component has both a positive and a negative direction. -/
theorem smul_Eplus_indefinite {σ : ℝ} (hσ : σ ≠ 0) :
    (∃ v : Fin 2 → ℝ, 0 < dotProduct v ((σ • Eplus).mulVec v)) ∧
      (∃ v : Fin 2 → ℝ, dotProduct v ((σ • Eplus).mulVec v) < 0) := by
  rcases lt_or_gt_of_ne hσ with hneg | hpos
  · constructor
    · refine ⟨![0, 1], ?_⟩
      simpa [smul_Eplus_quadratic] using neg_pos.mpr hneg
    · refine ⟨![1, 0], ?_⟩
      simpa [smul_Eplus_quadratic] using hneg
  · constructor
    · refine ⟨![1, 0], ?_⟩
      simpa [smul_Eplus_quadratic] using hpos
    · refine ⟨![0, 1], ?_⟩
      simpa [smul_Eplus_quadratic] using neg_neg_of_pos hpos

/-- The sign is positive for the owner's convention `Eplus * Eminus = J1`. -/
theorem smul_Eplus_Eminus_commutator (σ γ : ℝ) :
    (σ • Eplus) * (γ • Eminus) - (γ • Eminus) * (σ • Eplus) =
      (2 * σ * γ) • J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem smul_Eplus_Eminus_commute_iff (σ γ : ℝ) :
    (σ • Eplus) * (γ • Eminus) = (γ • Eminus) * (σ • Eplus) ↔
      σ = 0 ∨ γ = 0 := by
  rw [← sub_eq_zero, smul_Eplus_Eminus_commutator]
  constructor
  · intro h
    have h₀₁ := congrArg (fun A : Mat2 => A 0 1) h
    have hmul : 2 * σ * γ = 0 := by simpa [J1] using h₀₁
    rcases mul_eq_zero.mp hmul with hσ | hγ
    · left
      linarith
    · exact Or.inr hγ
  · rintro (rfl | rfl) <;> simp

/-- The existing general normality theorem specializes to the two coordinate axes. -/
theorem gen_isStarNormal_iff (σ γ : ℝ) :
    IsStarNormal (gen (σ, γ)) ↔ σ = 0 ∨ γ = 0 := by
  rw [InfoGeometry.OperatorAlgebra.RealMatrixSplit.isStarNormal_iff_parts_commute,
    gen_selfAdjointPart, gen_skewAdjointPart, commute_iff_eq]
  exact smul_Eplus_Eminus_commute_iff σ γ

/-- The mirror reverses both coordinates of the Clifford pencil. -/
theorem gen_mirror_conjugate (σ γ : ℝ) :
    J1 * gen (σ, γ) * J1 = -gen (σ, γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem gen_det (σ γ : ℝ) :
    (gen (σ, γ)).det = γ ^ 2 - σ ^ 2 := by
  simp [gen, Eplus, Eminus, Matrix.det_fin_two]
  ring

/-- Real-coordinate scalar multiplication with `Eminus` as a square root of `-1`.
Its first coordinate multiplies the identity, whereas `gen` uses `Eplus`. -/
def scalarPencil (σ γ : ℝ) : Mat2 := σ • (1 : Mat2) + γ • Eminus

/-- Multiplication of these real matrices follows the ordinary two-coordinate scalar law. -/
theorem scalarPencil_mul (σ γ τ δ : ℝ) :
    scalarPencil σ γ * scalarPencil τ δ =
      scalarPencil (σ * τ - γ * δ) (σ * δ + γ * τ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarPencil, Eminus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem scalarPencil_one : scalarPencil 1 0 = (1 : Mat2) := by
  simp [scalarPencil]

theorem scalarPencil_det (σ γ : ℝ) :
    (scalarPencil σ γ).det = σ ^ 2 + γ ^ 2 := by
  simp [scalarPencil, Eminus, Matrix.det_fin_two]
  ring

/-- The Clifford and scalar pencils agree precisely when the first coordinate vanishes. -/
theorem gen_eq_scalarPencil_iff (σ γ : ℝ) :
    gen (σ, γ) = scalarPencil σ γ ↔ σ = 0 := by
  constructor
  · intro h
    have h₁₁ := congrArg (fun A : Mat2 => A 1 1) h
    simp [gen, scalarPencil, Eplus, Eminus] at h₁₁
    linarith
  · rintro rfl
    simp [gen, scalarPencil]

/-- A nonzero null Clifford vector gives a nonzero matrix. -/
theorem gen_one_one_ne_zero : gen (1, 1) ≠ 0 := by
  intro h
  have h₀₀ := congrArg (fun A : Mat2 => A 0 0) h
  norm_num [gen, Eplus, Eminus] at h₀₀

/-- Reuse the Clifford generator square law for the nonzero nilpotent witness. -/
theorem gen_one_one_sq : gen (1, 1) * gen (1, 1) = 0 := by
  simpa [q11_apply] using gen_sq (1, 1)

theorem gen_one_one_isNilpotent : IsNilpotent (gen (1, 1)) := by
  refine ⟨2, ?_⟩
  simpa [pow_two] using gen_one_one_sq

/-- Vanishing symmetric part does not imply vanishing matrix action. -/
theorem gen_zero_one_nonstationary :
    (selfAdjointPart ℝ (gen (0, 1)) : Mat2) = 0 ∧
      (gen (0, 1)).mulVec ![1, 0] ≠ 0 := by
  constructor
  · simp [gen_selfAdjointPart]
  · intro h
    have h₁ := congrFun h 1
    norm_num [gen, Eplus, Eminus, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₁

end InfoGeometry.Clifford.Cl11Matrix
