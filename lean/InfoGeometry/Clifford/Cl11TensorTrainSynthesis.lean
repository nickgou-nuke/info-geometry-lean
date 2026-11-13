/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11RecursiveUnrolling
import InfoGeometry.Tensor.TensorTrainMatricization

/-!
# Exact Clifford reconstruction through actual tensor trains

The coefficient tensor is the output of the parity-corrected native Clifford
inverse. The train contracts those coefficients in physical site order; its
result is synthesized into the same native Clifford carrier and read back
through the constructed algebra equivalence.

The full-word construction retains one arbitrary real coefficient algebra.
The simultaneous minimal-bond construction is specialized to real scalar
coefficients, where the native matrix-rank theorems apply.
-/

namespace InfoGeometry.Clifford.Cl11TensorTrainSynthesis

open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Tensor.RankMinimalTensorTrain
open InfoGeometry.Tensor.TensorTrainMatricization

namespace TT

export InfoGeometry.Tensor.ExactTensorTrain (eval exists_exact_train)

end TT

universe u
variable (B : Type u) [Ring B] [Algebra ℝ B]

/-- Contract an actual train and synthesize its coefficients in the native
Clifford algebra, retaining one terminal coefficient algebra. -/
noncomputable def trainSynthesis {n : ℕ} (T : Train B 4 n 1) :=
  wordReconstruct B n (fun word => T.coeff 0 word)

/-- Matrix readback of that same native Clifford synthesis. -/
noncomputable def trainMatrix {n : ℕ} (T : Train B 4 n 1) : CoefficientMatrix B n :=
  leftCoefficientEquiv B n (trainSynthesis B T)

@[simp] theorem wordCoefficient_trainMatrix {n : ℕ} (T : Train B 4 n 1) :
    wordCoefficientEquiv B n (trainMatrix B T) = fun word => T.coeff 0 word := by
  simp [trainMatrix, trainSynthesis, wordReconstruct, unrollCoefficients]

/-- Exactness in matrix coordinates is equivalent to reconstruction of the
specific graded coefficient tensor, with no loss of any coefficient. -/
theorem trainMatrix_eq_iff {n : ℕ} (T : Train B 4 n 1) (M : CoefficientMatrix B n) :
    trainMatrix B T = M ↔
      T.coeff = Matrix.of (fun (_ : Fin 1) word => wordCoefficientEquiv B n M word) := by
  constructor
  · intro h
    have hcoeff := congrArg (wordCoefficientEquiv B n) h
    rw [wordCoefficient_trainMatrix] at hcoeff
    ext i word
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi, Matrix.of_apply] using congrFun hcoeff word
  · intro h
    apply (wordCoefficientEquiv B n).injective
    rw [wordCoefficient_trainMatrix]
    funext word
    exact congrArg (fun C : Matrix (Fin 1) (Words n) B => C 0 word) h

/-- Every matrix has an exact ordered full-word train, followed by native
graded Clifford synthesis and the original matrix readback. -/
theorem exists_exact_clifford_train (n : ℕ) (M : CoefficientMatrix B n) :
    ∃ left : Matrix Unit (Words n) B,
      ∃ core : Fin n → Fin 4 → Matrix (Words n) (Words n) B,
        ∃ right : Matrix (Words n) Unit B,
          leftCoefficientEquiv B n
            (wordReconstruct B n (TT.eval left core right)) = M := by
  obtain ⟨left, core, right, h⟩ := TT.exists_exact_train (wordCoefficientEquiv B n M)
  refine ⟨left, core, right, ?_⟩
  have hc : TT.eval left core right = wordCoefficientEquiv B n M := funext h
  rw [hc, wordReconstruct_coefficients]
  exact (leftCoefficientEquiv B n).apply_symm_apply M

/-- One compatible real train reconstructs the input matrix and attains
every positive cut rank. Every other train reconstructing that matrix has
at least those same bond dimensions. -/
theorem exists_minimal_clifford_train (n : ℕ) (M : CoefficientMatrix ℝ n) :
    ∃ T : Train ℝ 4 n 1,
      trainMatrix ℝ T = M ∧
      (∀ k : Fin n, T.bond k.succ =
        cutRank 4 n (Fin 1)
          (Matrix.of fun _ word => wordCoefficientEquiv ℝ n M word) k.succ) ∧
      (∀ S : Train ℝ 4 n 1, trainMatrix ℝ S = M →
        ∀ k : Fin n, T.bond k.succ ≤ S.bond k.succ) := by
  let C : Matrix (Fin 1) (Words n) ℝ :=
    Matrix.of fun _ word => wordCoefficientEquiv ℝ n M word
  obtain ⟨T, hT, hminimal⟩ := exists_rank_minimal_train 4 n 1 C
  refine ⟨T, (trainMatrix_eq_iff ℝ T M).mpr hT, hminimal, ?_⟩
  intro S hS k
  have hSC := (trainMatrix_eq_iff ℝ S M).mp hS
  rw [hminimal k, ← hSC]
  exact cutRank_coeff_le_bond S k.succ

/-- The cut invariant used in the compatible Clifford train has the native
four-letter dimension bound, with the actual prefix/suffix coordinate map
proved in `TensorTrainMatricization`. -/
theorem clifford_cutRank_le (m k : ℕ) (M : CoefficientMatrix ℝ (m + k)) :
    cutRank 4 (m + k) (Fin 1)
        (Matrix.of fun _ word => wordCoefficientEquiv ℝ (m + k) M word)
        ⟨k, Nat.lt_succ_of_le (Nat.le_add_left k m)⟩ ≤ 4 ^ min k m :=
  scalar_four_letter_cutRank_le m k (wordCoefficientEquiv ℝ (m + k) M)

end InfoGeometry.Clifford.Cl11TensorTrainSynthesis
