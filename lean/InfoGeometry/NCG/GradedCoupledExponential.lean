/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.EvenOddExponential
import InfoGeometry.NCG.BerezinianGaussianFactorization
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Coupled real block exponentials and their Gaussian factorization

The real scalar multiplying the grading is central. Arbitrary matrix-valued
diagonal coefficients instead produce the two explicit commutator defects.
The exponential is computed by convergent entire kernels of the actual square;
no matrix square root or inverse of a square root is used.

The existing block Gaussian factorization applies to the actual exponential.
For a real symmetric generator, positivity of its exponential proves the
required principal pivot invertible. Ordinary-real block factorization alone
does not extend the homogeneous-even Berezinian exponential law.
-/

noncomputable section

namespace InfoGeometry.NCG.GradedCoupledExponential

open Matrix
open InfoGeometry.Analysis.EvenOddExponential
open scoped MatrixOrder Matrix.Norms.L2Operator

-- The selected operator norm carries the rational scalar action inherited
-- through the real scalars; native exponential positivity uses this action.
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    NormedAlgebra ℚ (Matrix m m ℝ) where
  norm_smul_le r A := by
    rw [← IsScalarTower.algebraMap_smul ℝ r A]
    simpa only [norm_algebraMap'] using
      (norm_smul_le (algebraMap ℚ ℝ r) A)

variable {n R : Type*} [Fintype n] [DecidableEq n]

section Ring

variable [Ring R]

/-- The existing grading anticommutes with every off-diagonal block matrix. -/
theorem gamma_anticommutes_offDiagonal (U V : Matrix n n R) :
    (Gamma : Matrix (n ⊕ n) (n ⊕ n) R) * fromBlocks 0 U V 0 +
      fromBlocks 0 U V 0 * Gamma = 0 := by
  simp [Gamma, fromBlocks_multiply, fromBlocks_add]

/-- A noncentral diagonal block leaves both ordered commutator defects. -/
theorem coupled_square_with_commutators (B U V : Matrix n n R) :
    (fromBlocks B U V (-B)) ^ 2 =
      fromBlocks (B ^ 2 + U * V) (B * U - U * B)
        (V * B - B * V) (B ^ 2 + V * U) := by
  rw [pow_two, fromBlocks_multiply]
  apply fromBlocks_inj.mpr
  constructor
  · simp only [pow_two]
  constructor
  · noncomm_ring
  constructor <;> noncomm_ring

/-- The square is block diagonal precisely when the two commutators vanish. -/
theorem coupled_square_blockDiagonal_iff (B U V : Matrix n n R) :
    (fromBlocks B U V (-B)) ^ 2 =
        fromBlocks (B ^ 2 + U * V) 0 0 (B ^ 2 + V * U) ↔
      Commute B U ∧ Commute B V := by
  rw [coupled_square_with_commutators, fromBlocks_inj]
  simp only [true_and, and_true, sub_eq_zero, Commute, SemiconjBy]
  exact and_congr Iff.rfl eq_comm

end Ring

local notation "Mat" => Matrix n n ℝ
local notation "BlockMat" => Matrix (n ⊕ n) (n ⊕ n) ℝ

/-- A centrally scaled grading coupled to arbitrary full real matrix blocks. -/
def coupledGenerator (beta : ℝ) (U V : Mat) : BlockMat :=
  fromBlocks (beta • 1) U V (-(beta • 1))

omit [Fintype n] in
/-- The generator uses the existing block grading, with a real scalar action. -/
theorem coupledGenerator_eq (beta : ℝ) (U V : Mat) :
    coupledGenerator beta U V =
      beta • Gamma + fromBlocks 0 U V 0 := by
  simp [coupledGenerator, Gamma, fromBlocks_smul, fromBlocks_add]

/-- Centrality removes the defects without requiring U and V to commute. -/
theorem coupledGenerator_sq (beta : ℝ) (U V : Mat) :
    coupledGenerator beta U V ^ 2 =
      fromBlocks (beta ^ 2 • 1 + U * V) 0 0 (beta ^ 2 • 1 + V * U) := by
  rw [coupledGenerator, coupled_square_with_commutators]
  simp [pow_two, smul_smul]

omit [Fintype n] in
/-- Opposite off-diagonal blocks are actual transposes in the symmetric case. -/
theorem coupledGenerator_isHermitian (beta : ℝ) (U : Mat) :
    (coupledGenerator beta U Uᵀ).IsHermitian := by
  exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all beta)).fromBlocks
    (by simp) (Matrix.isHermitian_one.smul (IsSelfAdjoint.all beta)).neg

/-- The even-power entire kernel preserves block-diagonal support. -/
theorem evenExpKernel_fromBlocks (A D : Mat) :
    evenExpKernel (fromBlocks A 0 0 D) =
      fromBlocks (evenExpKernel A) 0 0 (evenExpKernel D) := by
  apply (summable_evenExpKernel (fromBlocks A 0 0 D)).hasSum.unique
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  rcases i with i | i <;> rcases j with j | j
  · simpa [evenExpKernel, fromBlocks_diagonal_pow, fromBlocks_smul] using
      Pi.hasSum.mp (Pi.hasSum.mp (summable_evenExpKernel A).hasSum i) j
  · simp [fromBlocks_diagonal_pow]
  · simp [fromBlocks_diagonal_pow]
  · simpa [evenExpKernel, fromBlocks_diagonal_pow, fromBlocks_smul] using
      Pi.hasSum.mp (Pi.hasSum.mp (summable_evenExpKernel D).hasSum i) j

/-- The odd-power coefficient kernel also preserves block-diagonal support. -/
theorem oddExpKernel_fromBlocks (A D : Mat) :
    oddExpKernel (fromBlocks A 0 0 D) =
      fromBlocks (oddExpKernel A) 0 0 (oddExpKernel D) := by
  apply (summable_oddExpKernel (fromBlocks A 0 0 D)).hasSum.unique
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  rcases i with i | i <;> rcases j with j | j
  · simpa [oddExpKernel, fromBlocks_diagonal_pow, fromBlocks_smul] using
      Pi.hasSum.mp (Pi.hasSum.mp (summable_oddExpKernel A).hasSum i) j
  · simp [fromBlocks_diagonal_pow]
  · simp [fromBlocks_diagonal_pow]
  · simpa [oddExpKernel, fromBlocks_diagonal_pow, fromBlocks_smul] using
      Pi.hasSum.mp (Pi.hasSum.mp (summable_oddExpKernel D).hasSum i) j

/-- The actual four-block exponential, preserving the order of U, V, and the
entire kernels. The squares may be singular or have negative spectrum. -/
theorem exp_neg_coupledGenerator (beta : ℝ) (U V : Mat) :
    NormedSpace.exp (-coupledGenerator beta U V) =
      fromBlocks
        (evenExpKernel (beta ^ 2 • 1 + U * V) -
          beta • oddExpKernel (beta ^ 2 • 1 + U * V))
        (-(U * oddExpKernel (beta ^ 2 • 1 + V * U)))
        (-(V * oddExpKernel (beta ^ 2 • 1 + U * V)))
        (evenExpKernel (beta ^ 2 • 1 + V * U) +
          beta • oddExpKernel (beta ^ 2 • 1 + V * U)) := by
  rw [exp_neg_eq_evenExpKernel_sub_mul_oddExpKernel, coupledGenerator_sq,
    evenExpKernel_fromBlocks, oddExpKernel_fromBlocks, coupledGenerator,
    fromBlocks_multiply]
  simp [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]

/-- The common scalar identity channel separates by centrality. -/
theorem exp_neg_add_smul_one (H : BlockMat) (alpha : ℝ) :
    NormedSpace.exp (-(H + alpha • 1)) =
      Real.exp (-alpha) • NormedSpace.exp (-H) := by
  have hcomm : Commute (-H) ((-alpha) • (1 : BlockMat)) :=
    (Commute.one_right (-H)).smul_right (-alpha)
  have hscalar : NormedSpace.exp ((-alpha) • (1 : BlockMat)) =
      Real.exp (-alpha) • (1 : BlockMat) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := BlockMat) (-alpha)).symm
  rw [neg_add, ← neg_smul, NormedSpace.exp_add_of_commute hcomm,
    hscalar, mul_smul_comm, mul_one]

/-- Positivity of the actual exponential of a symmetric real generator. -/
theorem exp_neg_posDef (H : BlockMat) (hH : H.IsHermitian) :
    (NormedSpace.exp (-H)).PosDef := by
  apply Matrix.isStrictlyPositive_iff_posDef.mp
  exact (NormedSpace.isUnit_exp (-H)).isStrictlyPositive hH.isSelfAdjoint.neg.exp_nonneg

/-- The lower-right principal block is positive definite, not just assumed
invertible as a consequence of invertibility of the whole exponential. -/
theorem exp_neg_pivot_posDef (H : BlockMat) (hH : H.IsHermitian) :
    (NormedSpace.exp (-H)).toBlocks₂₂.PosDef :=
  (exp_neg_posDef H hH).submatrix Sum.inr_injective

/-- The native nonsingular matrix inverse supplies both pivot inverse laws. -/
theorem exp_neg_pivot_twoSidedInverse (H : BlockMat) (hH : H.IsHermitian) :
    TwoSidedMatrixInverse (NormedSpace.exp (-H)).toBlocks₂₂
      (NormedSpace.exp (-H)).toBlocks₂₂⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (exp_neg_pivot_posDef H hH).isUnit
  exact ⟨Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet⟩

/-- The existing UDL factorization applied to a symmetric generator's actual
exponential, with its pivot inverse constructed by the preceding theorem. -/
theorem exp_neg_gaussian_factorization (H : BlockMat) (hH : H.IsHermitian) :
    NormedSpace.exp (-H) =
      berezinianUpperShear (NormedSpace.exp (-H)).toBlocks₁₂
          (NormedSpace.exp (-H)).toBlocks₂₂⁻¹ *
        berezinianSchurDiagonal (NormedSpace.exp (-H)).toBlocks₁₁
          (NormedSpace.exp (-H)).toBlocks₁₂ (NormedSpace.exp (-H)).toBlocks₂₁
          (NormedSpace.exp (-H)).toBlocks₂₂ (NormedSpace.exp (-H)).toBlocks₂₂⁻¹ *
        berezinianLowerShear (NormedSpace.exp (-H)).toBlocks₂₁
          (NormedSpace.exp (-H)).toBlocks₂₂⁻¹ := by
  simpa only [fromBlocks_toBlocks] using
    berezinian_block_gaussian_factorization
      (NormedSpace.exp (-H)).toBlocks₁₁ (NormedSpace.exp (-H)).toBlocks₁₂
      (NormedSpace.exp (-H)).toBlocks₂₁ (NormedSpace.exp (-H)).toBlocks₂₂
      (NormedSpace.exp (-H)).toBlocks₂₂⁻¹ (exp_neg_pivot_twoSidedInverse H hH)

/-- Noncommuting off-diagonal blocks occur even in the symmetric class where
the positive pivot and Gaussian factorization theorems apply. -/
theorem exists_symmetric_noncommuting_coupling :
    ∃ U V : Matrix (Fin 2) (Fin 2) ℝ,
      U * V ≠ V * U ∧ (coupledGenerator 1 U V).IsHermitian := by
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
  refine ⟨U, Uᵀ, ?_, coupledGenerator_isHermitian 1 U⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [U, Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- A genuinely matrix-valued diagonal coefficient can leave a nonzero
off-diagonal square, so scalar centrality cannot be discarded. -/
theorem exists_noncentral_square_defect :
    ∃ B U V : Matrix (Fin 2) (Fin 2) ℝ,
      ((fromBlocks B U V (-B)) ^ 2).toBlocks₁₂ ≠ 0 := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], 0, ?_⟩
  rw [coupled_square_with_commutators]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h01

end InfoGeometry.NCG.GradedCoupledExponential
