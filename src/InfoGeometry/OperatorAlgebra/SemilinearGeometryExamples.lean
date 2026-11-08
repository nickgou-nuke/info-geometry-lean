/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
import InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry
import InfoGeometry.OperatorAlgebra.CovarianceExamples
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Noncommuting witnesses for semilinear symmetry and ordered amplitudes

The four-dimensional example has full coupled blocks, a normalized invariant
Gram density, and an odd Hermitian observable which does not commute with
that density. Its odd expectation vanishes by the general theorem, while
its even Hamiltonian has strictly nonzero expectation.

The second example uses the existing full positive covariance matrix as a
unit amplitude. Its ordered second quotient is not Hermitian.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SemilinearGeometryExamples

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
open InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

def P : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]
def Q : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 2, 0]
def D : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem P_isHermitian : P.IsHermitian := by
  change Pᴴ = P
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P]

theorem Q_isHermitian : Q.IsHermitian := by
  change Qᴴ = Q
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q]

def evenHamiltonian : SheetMatrix (Fin 2) := Matrix.fromBlocks P Q Q P
def gramDensity : SheetMatrix (Fin 2) :=
  (1 / 38 : ℝ) • (evenHamiltonian * star evenHamiltonian)
def oddObservable : SheetMatrix (Fin 2) := Matrix.fromBlocks P D (star D) (-P)

theorem evenHamiltonian_isHermitian : evenHamiltonian.IsHermitian := by
  rw [evenHamiltonian, Matrix.isHermitian_fromBlocks_iff]
  exact ⟨P_isHermitian, Q_isHermitian.eq, Q_isHermitian.eq, P_isHermitian⟩

theorem evenHamiltonian_even : sheetConj evenHamiltonian = evenHamiltonian := by
  have h : sheetConj (Matrix.fromBlocks P Q Qᴴ P) = Matrix.fromBlocks P Q Qᴴ P := by
    apply (sheetConj_coupledBlock_even_iff P Q P).mpr
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [P, Q, starRingEnd_apply]
  simpa only [evenHamiltonian, Q_isHermitian.eq] using h

theorem gramDensity_posSemidef : gramDensity.PosSemidef := by
  exact (Matrix.posSemidef_self_mul_conjTranspose evenHamiltonian).smul (by norm_num)

theorem gramDensity_isHermitian : gramDensity.IsHermitian :=
  gramDensity_posSemidef.isHermitian

theorem gramDensity_even : sheetConj gramDensity = gramDensity := by
  simp only [gramDensity, map_smul, sheetConj_mul, sheetConj_star, evenHamiltonian_even]

theorem oddObservable_isHermitian : oddObservable.IsHermitian := by
  apply (coupledBlock_isHermitian_iff P D (-P)).mpr
  exact ⟨P_isHermitian, P_isHermitian.neg⟩

theorem oddObservable_odd : sheetConj oddObservable = -oddObservable := by
  apply (sheetConj_coupledBlock_odd_iff P D (-P)).mpr
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, D, starRingEnd_apply]

/-- The Gram blocks retain the noncommuting products of the original two blocks. -/
theorem evenHamiltonian_square : evenHamiltonian * evenHamiltonian =
    Matrix.fromBlocks !![10, 6; 6, 9] !![8, 9; 9, 4]
      !![8, 9; 9, 4] !![10, 6; 6, 9] := by
  rw [evenHamiltonian, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Q, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two]

theorem evenHamiltonian_square_trace :
    Matrix.trace (evenHamiltonian * evenHamiltonian) = 38 := by
  rw [evenHamiltonian_square]
  norm_num [Matrix.trace, Matrix.diag, Matrix.fromBlocks,
    Fintype.sum_sum_type, Fin.sum_univ_two]

theorem gramDensity_trace_one : Matrix.trace gramDensity = 1 := by
  rw [gramDensity, Matrix.trace_smul, evenHamiltonian_isHermitian.star_eq,
    evenHamiltonian_square_trace]
  norm_num [Complex.real_smul]

/-- The vanishing odd expectation is not obtained from a commuting density. -/
theorem gramDensity_oddObservable_noncommute :
    gramDensity * oddObservable ≠ oddObservable * gramDensity := by
  intro h
  have hentry := congrArg
    (fun X : SheetMatrix (Fin 2) => X (Sum.inl 0) (Sum.inl 1)) h
  norm_num [gramDensity, evenHamiltonian_isHermitian.star_eq, evenHamiltonian_square,
    oddObservable, P, D, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Complex.real_smul] at hentry

/-- The general symmetry theorem proves the cancellation on this noncommuting pair. -/
theorem odd_expectation_zero : Matrix.trace (gramDensity * oddObservable) = 0 :=
  trace_mul_eq_zero_of_even_odd gramDensity_isHermitian oddObservable_isHermitian
    gramDensity_even oddObservable_odd

def energyHamiltonian : SheetMatrix (Fin 2) :=
  Matrix.fromBlocks P (P + Q) (P + Q) P

theorem energyHamiltonian_isHermitian : energyHamiltonian.IsHermitian := by
  rw [energyHamiltonian, Matrix.isHermitian_fromBlocks_iff]
  exact ⟨P_isHermitian, (P_isHermitian.add Q_isHermitian).eq,
    (P_isHermitian.add Q_isHermitian).eq, P_isHermitian⟩

theorem energyHamiltonian_even : sheetConj energyHamiltonian = energyHamiltonian := by
  have h : sheetConj (Matrix.fromBlocks P (P + Q) (P + Q)ᴴ P) =
      Matrix.fromBlocks P (P + Q) (P + Q)ᴴ P := by
    apply (sheetConj_coupledBlock_even_iff P (P + Q) P).mpr
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [P, Q, starRingEnd_apply]
  simpa only [energyHamiltonian, (P_isHermitian.add Q_isHermitian).eq] using h

theorem gramDensity_energyHamiltonian_noncommute :
    gramDensity * energyHamiltonian ≠ energyHamiltonian * gramDensity := by
  intro h
  have hentry := congrArg
    (fun X : SheetMatrix (Fin 2) => X (Sum.inl 0) (Sum.inl 1)) h
  norm_num [gramDensity, evenHamiltonian_isHermitian.star_eq, evenHamiltonian_square,
    energyHamiltonian, P, Q, Matrix.fromBlocks, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Complex.real_smul] at hentry

/-- Invariance does not force zero energy, even for a noncommuting density-observable pair. -/
theorem noncommuting_even_energy :
    Matrix.trace (gramDensity * energyHamiltonian) = (136 / 19 : ℂ) := by
  rw [gramDensity, evenHamiltonian_isHermitian.star_eq, smul_mul_assoc,
    Matrix.trace_smul, evenHamiltonian_square]
  norm_num [energyHamiltonian, P, Q, Matrix.trace, Matrix.diag, Matrix.fromBlocks,
    Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Complex.real_smul]

theorem noncommuting_even_energy_ne_zero :
    Matrix.trace (gramDensity * energyHamiltonian) ≠ 0 := by
  rw [noncommuting_even_energy]
  norm_num

/-- The existing full positive covariance supplies a genuine invertible amplitude. -/
def positiveAmplitude : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := CovarianceExamples.noise
  inv := !![1, -1; -1, 2]
  val_inv := by
    rw [CovarianceExamples.noise_entries]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    rw [CovarianceExamples.noise_entries]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem positiveAmplitude_posSemidef :
    (positiveAmplitude : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef :=
  CovarianceExamples.noise_posSemidef

theorem amplitude_generator_noncommute :
    Q * (positiveAmplitude : Matrix (Fin 2) (Fin 2) ℂ) ≠
      (positiveAmplitude : Matrix (Fin 2) (Fin 2) ℂ) * Q := by
  intro h
  have hentry := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 1) h
  norm_num [Q, positiveAmplitude, CovarianceExamples.noise_entries,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The quotient is computed with its right inverse in the specified order. -/
theorem amplitudeQuotient_entries :
    matrixAmplitudeQuotient Q positiveAmplitude = !![5, -6; 3, -7] := by
  rw [matrixAmplitudeQuotient_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ring.lie_def, Q, positiveAmplitude, CovarianceExamples.noise_entries,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem amplitudeQuotient_not_hermitian :
    ¬ (matrixAmplitudeQuotient Q positiveAmplitude).IsHermitian := by
  intro h
  have hentry := h.apply 0 1
  norm_num [amplitudeQuotient_entries] at hentry

end InfoGeometry.OperatorAlgebra.SemilinearGeometryExamples
