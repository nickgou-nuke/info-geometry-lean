/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure
import InfoGeometry.Canonical.MajoranaCoefficientAction
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Explicit two-site Jordan–Wigner matrices built from the existing CAR pair. -/
namespace InfoGeometry.Canonical.CARMajoranaFiniteBridge

open scoped BigOperators Kronecker
open InfoGeometry.MajoranaPfaffianNaturalClosure
open MajoranaCoefficientAction
open KitaevChainMajoranaZeroModes

noncomputable section

/-- The first Majorana is the complexified sum of the existing CAR units. -/
theorem majorana1_from_car :
    majorana1 = annihilationR.map (algebraMap ℝ ℂ) +
      creationR.map (algebraMap ℝ ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana1, splitPos, annihilationR, creationR]

/-- The negative real split generator needs an explicit imaginary factor. -/
theorem majorana2_from_car :
    majorana2 = (-Complex.I) •
      (annihilationR.map (algebraMap ℝ ℂ) - creationR.map (algebraMap ℝ ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana2, splitNeg, annihilationR, creationR]

/-- Parity of the same concrete CAR pair. -/
def parityMatrix : M2C :=
  (annihilationR * creationR - creationR * annihilationR).map (algebraMap ℝ ℂ)

abbrev ChainOp := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Two-site Jordan-Wigner family on the full complex spin space. -/
def twoSiteMajorana : Fin 4 → ChainOp :=
  ![majorana1 ⊗ₖ (1 : M2C), majorana2 ⊗ₖ (1 : M2C),
    parityMatrix ⊗ₖ majorana1, parityMatrix ⊗ₖ majorana2]

set_option maxHeartbeats 2000000 in
/-- Full cross-site CAR, not merely the single-site square identities. -/
theorem twoSiteMajorana_car (a b : Fin 4) :
    twoSiteMajorana a * twoSiteMajorana b + twoSiteMajorana b * twoSiteMajorana a =
      if a = b then 2 else 0 := by
  rw [show (2 : ChainOp) = 1 + 1 by norm_num]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases b <;>
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [twoSiteMajorana, parityMatrix, majorana1, majorana2,
      splitPos, splitNeg, annihilationR, creationR, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem twoSiteMajorana_selfAdjoint (i : Fin 4) :
    (twoSiteMajorana i).conjTranspose = twoSiteMajorana i := by
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases i <;> fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    norm_num [twoSiteMajorana, parityMatrix, majorana1, majorana2,
      splitPos, splitNeg, annihilationR, creationR, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem twoSiteMajorana_ne_zero (i : Fin 4) : twoSiteMajorana i ≠ 0 := by
  intro hz
  have heq : Fintype.linearCombination ℝ twoSiteMajorana (Pi.single i 1) =
      Fintype.linearCombination ℝ twoSiteMajorana 0 := by
    simpa only [Fintype.linearCombination_apply_single, one_smul, map_zero] using hz
  have hs := linearCombination_injective twoSiteMajorana_car heq
  have he := congrFun hs i
  simp at he

end
end InfoGeometry.Canonical.CARMajoranaFiniteBridge
