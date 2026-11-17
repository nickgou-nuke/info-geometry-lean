/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Positive real domain-wall transfer matrices

The full block matrix `T(B,C)` is the ordered congruence
`U(C)ᴴ * diag(B⁻¹,B) * U(C)`. For positive definite `B` it is positive
definite and has determinant one, with no commutation assumption on `B` and
`C`. The shear inverse is explicit. Over `ℝ`, conjugate transpose is transpose.

The Wilson block is constructed as a positive mass plus a sum of actual
matrix Gram squares. For orthogonal link operators it equals the conventional
hopping expression. This proves the matrix lower bound without replacing the
operator algebra by scalar eigenvalues or assuming simultaneous diagonalization.

These are finite-dimensional operator theorems. No logarithm, spectral sign,
infinite transfer limit, Fock vacuum, or determinant-line section is supplied.
The block formula is the real-adjoint version of equation (2.14) in
Narayanan--Neuberger, <https://arxiv.org/abs/hep-lat/9307006>.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDomainWallTransfer

open Matrix
open scoped BigOperators

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The quadratic form of an actual two-block diagonal matrix splits into its blocks. -/
theorem blockDiagonal_quadratic (A : Matrix n n ℝ) (B : Matrix m m ℝ)
    (x : n ⊕ m → ℝ) :
    star x ⬝ᵥ (fromBlocks A 0 0 B *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
  simpa only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add] using
    (Matrix.dotProduct_block (star x) (fromBlocks A 0 0 B *ᵥ x))

/-- Strict positivity survives a direct sum, including empty index types. -/
theorem posDef_fromBlocks_diagonal {A : Matrix n n ℝ} {B : Matrix m m ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (fromBlocks A 0 0 B).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (hA.isHermitian.fromBlocks (by simp) hB.isHermitian) ?_
  intro x hx
  rw [blockDiagonal_quadratic]
  by_cases hleft : x ∘ Sum.inl = 0
  · have hright : x ∘ Sum.inr ≠ 0 := by
      intro hright
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hleft i
      | inr i => exact congrFun hright i
    have hpos := hB.dotProduct_mulVec_pos hright
    simpa only [hleft, star_zero, zero_dotProduct, zero_add] using hpos
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hleft)
      (hB.posSemidef.dotProduct_mulVec_nonneg _)

variable [DecidableEq n]

/-- An upper unitriangular shear in the full doubled matrix algebra. -/
def upperShear (C : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks 1 C 0 1

/-- Negating the off-diagonal block is an actual right inverse. -/
theorem upperShear_mul_neg (C : Matrix n n ℝ) :
    upperShear C * upperShear (-C) = 1 := by
  simp [upperShear, fromBlocks_multiply, fromBlocks_one]

/-- Negating the off-diagonal block is also an actual left inverse. -/
theorem upperShear_neg_mul (C : Matrix n n ℝ) :
    upperShear (-C) * upperShear C = 1 := by
  simpa only [neg_neg] using upperShear_mul_neg (-C)

/-- The shear is a unit, without any assumption on its off-diagonal block. -/
theorem upperShear_isUnit (C : Matrix n n ℝ) : IsUnit (upperShear C) := by
  exact ⟨⟨upperShear C, upperShear (-C), upperShear_mul_neg C,
    upperShear_neg_mul C⟩, rfl⟩

/-- Both diagonal blocks are identities, so the shear has determinant one. -/
theorem upperShear_det (C : Matrix n n ℝ) : (upperShear C).det = 1 := by
  simp only [upperShear, det_fromBlocks_zero₂₁, det_one, one_mul]

/-- The ordered transfer matrix. Its inverse block is Mathlib's native matrix inverse. -/
def transfer (B C : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks B⁻¹ (B⁻¹ * C) (Cᴴ * B⁻¹) (Cᴴ * B⁻¹ * C + B)

/-- Ordered congruence factorization; it does not commute the two input matrices. -/
theorem transfer_eq_congruence (B C : Matrix n n ℝ) :
    transfer B C =
      (upperShear C)ᴴ * fromBlocks B⁻¹ 0 0 B * upperShear C := by
  simp only [transfer, upperShear, fromBlocks_conjTranspose, conjTranspose_one,
    conjTranspose_zero, fromBlocks_multiply, one_mul, mul_one, zero_mul,
    mul_zero, add_zero, zero_add]

/-- A positive definite Wilson block gives a positive definite full transfer matrix. -/
theorem transfer_posDef {B : Matrix n n ℝ} (hB : B.PosDef) (C : Matrix n n ℝ) :
    (transfer B C).PosDef := by
  rw [transfer_eq_congruence]
  exact (posDef_fromBlocks_diagonal hB.inv hB).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (upperShear_isUnit C))

/-- The two diagonal determinants cancel; positivity supplies the genuine inverse law. -/
theorem transfer_det {B : Matrix n n ℝ} (hB : B.PosDef) (C : Matrix n n ℝ) :
    (transfer B C).det = 1 := by
  rw [transfer_eq_congruence]
  simp only [det_mul, det_conjTranspose, upperShear_det, star_one, one_mul, mul_one,
    det_fromBlocks_zero₂₁]
  exact B.det_nonsing_inv_mul_det ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit)

section Wilson

variable {ι : Type*} [Fintype ι]

/-- The actual link difference Gram matrix, with no orthogonality assumption needed. -/
def linkGram (U : ι → Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • ∑ i, (1 - U i)ᴴ * (1 - U i)

/-- Every summand is a native matrix Gram square. -/
theorem linkGram_posSemidef (U : ι → Matrix n n ℝ) : (linkGram U).PosSemidef := by
  have hsum : (∑ i, (1 - U i)ᴴ * (1 - U i)).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ =>
      Matrix.posSemidef_conjTranspose_mul_self (1 - U i)
  exact hsum.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- A mass term plus the full link Gram matrix. -/
def wilsonBlock (c : ℝ) (U : ι → Matrix n n ℝ) : Matrix n n ℝ :=
  c • 1 + linkGram U

/-- Positive mass gives strict positivity for every link family. -/
theorem wilsonBlock_posDef {c : ℝ} (hc : 0 < c) (U : ι → Matrix n n ℝ) :
    (wilsonBlock c U).PosDef :=
  (Matrix.PosDef.one.smul hc).add_posSemidef (linkGram_posSemidef U)

/-- An orthogonal link turns its Gram square into the usual hopping summand. -/
theorem link_square_eq (U : Matrix n n ℝ) (hU : Uᴴ * U = 1) :
    (1 - U)ᴴ * (1 - U) = (2 : ℝ) • (1 : Matrix n n ℝ) - (U + Uᴴ) := by
  simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub,
    one_mul, mul_one, hU, two_smul]
  abel

/-- For orthogonal links the Gram construction is exactly the Wilson hopping block. -/
theorem wilsonBlock_eq_hopping (c : ℝ) (U : ι → Matrix n n ℝ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) :
    wilsonBlock c U =
      (c + Fintype.card ι : ℝ) • (1 : Matrix n n ℝ) -
        (1 / 2 : ℝ) • ∑ i, (U i + (U i)ᴴ) := by
  unfold wilsonBlock linkGram
  simp_rw [link_square_eq _ (hU _)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ]
  module

/-- The matrix lower bound retains the quadratic form on every real vector. -/
theorem wilsonBlock_quadratic_lower (c : ℝ) (U : ι → Matrix n n ℝ) (x : n → ℝ) :
    c * (star x ⬝ᵥ x) ≤ star x ⬝ᵥ (wilsonBlock c U *ᵥ x) := by
  have h := (linkGram_posSemidef U).dotProduct_mulVec_nonneg x
  simpa only [wilsonBlock, add_mulVec, smul_mulVec, one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul] using
      le_add_of_nonneg_right h (a := c * (star x ⬝ᵥ x))

/-- Positive Wilson mass closes both transfer conclusions for arbitrary hopping `C`. -/
theorem wilson_transfer (c : ℝ) (hc : 0 < c) (U : ι → Matrix n n ℝ)
    (C : Matrix n n ℝ) :
    (transfer (wilsonBlock c U) C).PosDef ∧
      (transfer (wilsonBlock c U) C).det = 1 :=
  ⟨transfer_posDef (wilsonBlock_posDef hc U) C,
    transfer_det (wilsonBlock_posDef hc U) C⟩

end Wilson

/-- A positive block for the closed noncommuting witness. -/
def witnessB : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2, 3]

/-- An off-diagonal block which does not commute with `witnessB`. -/
def witnessC : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem witnessB_posDef : witnessB.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

/-- The positivity and determinant results apply to an explicitly noncommuting pair. -/
theorem noncommuting_transfer_witness :
    witnessB * witnessC ≠ witnessC * witnessB ∧
      (transfer witnessB witnessC).PosDef ∧ (transfer witnessB witnessC).det = 1 := by
  refine ⟨?_, transfer_posDef witnessB_posDef witnessC, transfer_det witnessB_posDef witnessC⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [witnessB, witnessC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at h01

end InfoGeometry.Canonical.RealDomainWallTransfer
