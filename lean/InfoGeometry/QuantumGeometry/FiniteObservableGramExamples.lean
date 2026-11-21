/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.QuantumGeometry.FiniteObservableGramCongruence

/-!
# A noncommuting two-observable example

The existing finite spin raising and lowering matrices give two Hermitian
observables.  In the first coordinate state their uncertainty Gram matrix is
`[[1,I],[-I,1]]`, so the imaginary commutator term is nonzero.
-/

noncomputable section

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open scoped InnerProductSpace ComplexOrder

namespace InfoGeometry.QuantumGeometry.FiniteObservableGram.Examples

def state : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]

def observables : Fin 2 → Mat2C :=
  ![J_plus + J_minus, (-Complex.I) • (J_plus - J_minus)]

theorem state_normalized : ⟪state, state⟫_ℂ = 1 := by
  have hs : state = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [state]
  rw [hs, EuclideanSpace.inner_single_left]
  simp

theorem observables_isHermitian (a : Fin 2) : (observables a).IsHermitian := by
  change (observables a)ᴴ = observables a
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [observables, J_plus, J_minus, Matrix.conjTranspose_apply]

theorem observables_do_not_commute : observables 0 * observables 1 ≠
    observables 1 * observables 0 := by
  intro h
  have him := congrArg (fun M : Mat2C => (M 0 0).im) h
  norm_num [observables, J_plus, J_minus, Matrix.mul_apply,
    Fin.sum_univ_two] at him

theorem fluctuationColumns_explicit : fluctuationColumns state observables =
    !![0, 0; 1, Complex.I] := by
  ext i a
  fin_cases i <;> fin_cases a <;>
    norm_num [fluctuationColumns, fluctuation, expectation,
      observables, state, J_plus, J_minus, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      PiLp.inner_apply, Fin.sum_univ_two]

theorem uncertaintyGram_explicit : uncertaintyGram state observables =
    !![1, Complex.I; -Complex.I, 1] := by
  rw [uncertaintyGram_eq_rightGram, fluctuationColumns_explicit]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [InfoGeometry.Krein.FiniteDiracGramSquare.rightGram,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem covariance_explicit : covariance state observables = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [covariance, uncertaintyGram_explicit]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num

theorem commutatorMatrix_explicit : commutatorMatrix state observables =
    !![0, 1; -1, 0] := by
  rw [commutatorMatrix_eq_im state state_normalized observables observables_isHermitian,
    uncertaintyGram_explicit]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num

end InfoGeometry.QuantumGeometry.FiniteObservableGram.Examples

end
