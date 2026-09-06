import InfoGeometry.OperatorAlgebra.ThreeModeChiralFockSplitOctonionBridge

/-!
# Finite CAR modular eigenmodes

The diagonal Bernoulli/Cantor trace is modularly trivial on its diagonal
algebra.  This file therefore records only the finite full-matrix generator
whose off-diagonal CAR channels have opposite frequencies.  It is an
algebraic commutator statement, not a claim of a global von Neumann modular
flow.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LocalCARModularEigenmodes

open Matrix
open InfoGeometry.Canonical.CantorLocalCl11HopParity
open InfoGeometry.Canonical.SplitCliffordCantorFock

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def thermalHamiltonian (ε : ℝ) : M2R := ε • localNumberOperator

def modularGenerator (ε : ℝ) (X : M2R) : M2R :=
  thermalHamiltonian ε * X - X * thermalHamiltonian ε

theorem modularGenerator_plus_projection (ε : ℝ) :
    modularGenerator ε localPlusProjection = 0 := by
  rw [localPlusProjection_eq_localVacuumProjection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularGenerator, thermalHamiltonian,
      localNumberOperator, localVacuumProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularGenerator_minus_projection (ε : ℝ) :
    modularGenerator ε localMinusProjection = 0 := by
  rw [localMinusProjection_eq_localOccupiedProjection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularGenerator, thermalHamiltonian,
      localNumberOperator, localOccupiedProjection, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularGenerator_annihilation (ε : ℝ) :
    modularGenerator ε a_op = -(ε • a_op) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularGenerator, thermalHamiltonian,
      localNumberOperator, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularGenerator_creation (ε : ℝ) :
    modularGenerator ε aDag_op = ε • aDag_op := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularGenerator, thermalHamiltonian,
      localNumberOperator, a_op, aDag_op,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modular_eigenmode_packet (ε : ℝ) :
    modularGenerator ε localPlusProjection = 0 ∧
    modularGenerator ε localMinusProjection = 0 ∧
    modularGenerator ε a_op = -(ε • a_op) ∧
    modularGenerator ε aDag_op = ε • aDag_op := by
  exact ⟨modularGenerator_plus_projection ε,
    modularGenerator_minus_projection ε,
    modularGenerator_annihilation ε,
    modularGenerator_creation ε⟩

end InfoGeometry.OperatorAlgebra.LocalCARModularEigenmodes
