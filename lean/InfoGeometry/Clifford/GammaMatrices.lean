import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Clifford.Cl11Matrix

/-!
# Split `Cl(1,1)` gamma matrix interface

This module exposes the concrete split `Cl(1,1)` matrix atom owned by
`InfoGeometry.Clifford.Cl11Matrix` under the gamma names used by the recursive
spinor representation.  It also defines the recursive tensor index for the
`2^n` spinor matrix stages.
-/

noncomputable section

namespace InfoGeometry.Clifford.GammaMatrices

open Matrix
open InfoGeometry.Clifford

/-- Recursive tensor index for the real `2^n` spinor stage. -/
def TensorIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => TensorIndex n × Fin 2

instance tensorIndexFintype : (n : ℕ) → Fintype (TensorIndex n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
      let _ : Fintype (TensorIndex n) := tensorIndexFintype n
      inferInstanceAs (Fintype (TensorIndex n × Fin 2))

instance tensorIndexDecidableEq : (n : ℕ) → DecidableEq (TensorIndex n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 =>
      let _ : DecidableEq (TensorIndex n) := tensorIndexDecidableEq n
      inferInstanceAs (DecidableEq (TensorIndex n × Fin 2))

/-- Matrix algebra acting on the `n`-fold real split spinor tensor stage. -/
abbrev SplitGammaMatrix (n : ℕ) :=
  Matrix (TensorIndex n) (TensorIndex n) ℝ

/-- Positive split generator, inherited from the proven `Cl(1,1)` matrix atom. -/
abbrev gammaPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  Cl11Matrix.Eplus

/-- Negative split generator, inherited from the proven `Cl(1,1)` matrix atom. -/
abbrev gammaMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  Cl11Matrix.Eminus

/-- Local grading/chirality atom `γ₊γ₋`. -/
abbrev gamma12 : Matrix (Fin 2) (Fin 2) ℝ :=
  Cl11Matrix.J1

@[simp] theorem gammaPlus_sq :
    gammaPlus * gammaPlus = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  Cl11Matrix.Eplus_sq

@[simp] theorem gammaMinus_sq :
    gammaMinus * gammaMinus = -1 • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  Cl11Matrix.Eminus_sq

@[simp] theorem gamma12_sq :
    gamma12 * gamma12 = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  Cl11Matrix.J1_sq

/-- Readback of the chirality atom as the product of the split generators. -/
theorem gamma12_eq :
    gamma12 = gammaPlus * gammaMinus :=
  (Cl11Matrix.Eplus_mul_Eminus).symm

theorem gammaPlus_gammaMinus_anticomm :
    gammaPlus * gammaMinus + gammaMinus * gammaPlus =
      (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gammaPlus, gammaMinus, Cl11Matrix.Eplus,
      Cl11Matrix.Eminus, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

theorem gamma12_gammaPlus_anticomm :
    gamma12 * gammaPlus + gammaPlus * gamma12 =
      (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma12, gammaPlus, Cl11Matrix.J1,
      Cl11Matrix.Eplus, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

theorem gamma12_gammaMinus_anticomm :
    gamma12 * gammaMinus + gammaMinus * gamma12 =
      (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma12, gammaMinus, Cl11Matrix.J1,
      Cl11Matrix.Eminus, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

end InfoGeometry.Clifford.GammaMatrices
