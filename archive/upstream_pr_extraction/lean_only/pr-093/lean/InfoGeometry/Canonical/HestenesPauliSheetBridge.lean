import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Canonical.ChiralStokesPauliBasis

noncomputable section

namespace InfoGeometry.Canonical.HestenesPauliSheetBridge

open InfoGeometry.Canonical.ChiralStokesPauliBasis

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-!
This owner is the finite matrix Hestenes dictionary.  It records the real
Clifford reading of the Pauli sheet basis without claiming an unproved
isomorphism with an abstract even Clifford subalgebra.
-/

def hestenesScalar : M2C :=
  InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetIdentity

def hestenesParity : M2C :=
  InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity

def hestenesExchange : M2C :=
  InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetFlip

def hestenesPhase : M2C :=
  InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetPhase

def circularPlus : M2C :=
  ((2 : ℂ)⁻¹) • (hestenesExchange + Complex.I • hestenesPhase)

def circularMinus : M2C :=
  ((2 : ℂ)⁻¹) • (hestenesExchange - Complex.I • hestenesPhase)

theorem hestenesScalar_eq_one : hestenesScalar = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, ChiralStokesPauliBasis.sheetIdentity,
      Matrix.one_apply]

theorem hestenesParity_sq : hestenesParity * hestenesParity = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesParity, ChiralStokesPauliBasis.sheetParity,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem hestenesExchange_sq : hestenesExchange * hestenesExchange = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesExchange, ChiralStokesPauliBasis.sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem hestenesPhase_sq : hestenesPhase * hestenesPhase = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesPhase, ChiralStokesPauliBasis.sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I]

theorem hestenesParity_exchange_anticommute :
    hestenesParity * hestenesExchange =
      -(hestenesExchange * hestenesParity) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesParity, hestenesExchange,
      ChiralStokesPauliBasis.sheetParity, ChiralStokesPauliBasis.sheetFlip,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem hestenesParity_phase_anticommute :
    hestenesParity * hestenesPhase =
      -(hestenesPhase * hestenesParity) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesParity, hestenesPhase,
      ChiralStokesPauliBasis.sheetParity, ChiralStokesPauliBasis.sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem hestenesExchange_phase_anticommute :
    hestenesExchange * hestenesPhase =
      -(hestenesPhase * hestenesExchange) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesExchange, hestenesPhase,
      ChiralStokesPauliBasis.sheetFlip, ChiralStokesPauliBasis.sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem circularPlus_eq_sigmaPlus :
    circularPlus = TwoSheetThreeColorWeyl.sigmaPlus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [circularPlus, hestenesExchange, hestenesPhase,
      ChiralStokesPauliBasis.sheetFlip, ChiralStokesPauliBasis.sheetPhase,
      TwoSheetThreeColorWeyl.sigmaPlus, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Complex.I_mul_I] <;> ring

theorem circularMinus_eq_sigmaMinus :
    circularMinus = TwoSheetThreeColorWeyl.sigmaMinus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [circularMinus, hestenesExchange, hestenesPhase,
      ChiralStokesPauliBasis.sheetFlip, ChiralStokesPauliBasis.sheetPhase,
      TwoSheetThreeColorWeyl.sigmaMinus, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Complex.I_mul_I] <;> ring

theorem circularPlus_sq : circularPlus * circularPlus = 0 := by
  rw [circularPlus_eq_sigmaPlus]
  exact TwoSheetThreeColorWeyl.sigmaPlus_sq

theorem circularMinus_sq : circularMinus * circularMinus = 0 := by
  rw [circularMinus_eq_sigmaMinus]
  exact TwoSheetThreeColorWeyl.sigmaMinus_sq

theorem circularPlus_mul_circularMinus :
    circularPlus * circularMinus =
      ((2 : ℂ)⁻¹) • (hestenesScalar + hestenesParity) := by
  rw [circularPlus_eq_sigmaPlus, circularMinus_eq_sigmaMinus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, hestenesParity,
      ChiralStokesPauliBasis.sheetIdentity, ChiralStokesPauliBasis.sheetParity,
      TwoSheetThreeColorWeyl.sigmaPlus, TwoSheetThreeColorWeyl.sigmaMinus,
      Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply] <;> norm_num

theorem circularMinus_mul_circularPlus :
    circularMinus * circularPlus =
      ((2 : ℂ)⁻¹) • (hestenesScalar - hestenesParity) := by
  rw [circularPlus_eq_sigmaPlus, circularMinus_eq_sigmaMinus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, hestenesParity,
      ChiralStokesPauliBasis.sheetIdentity, ChiralStokesPauliBasis.sheetParity,
      TwoSheetThreeColorWeyl.sigmaPlus, TwoSheetThreeColorWeyl.sigmaMinus,
      Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply] <;> norm_num

theorem circular_anticommutator :
    circularPlus * circularMinus + circularMinus * circularPlus =
      hestenesScalar := by
  rw [circularPlus_eq_sigmaPlus, circularMinus_eq_sigmaMinus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, ChiralStokesPauliBasis.sheetIdentity,
      TwoSheetThreeColorWeyl.sigmaPlus, TwoSheetThreeColorWeyl.sigmaMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem circular_idempotents_sum :
    ((2 : ℂ)⁻¹) • (hestenesScalar + hestenesParity) +
        ((2 : ℂ)⁻¹) • (hestenesScalar - hestenesParity) =
      hestenesScalar := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, hestenesParity,
      ChiralStokesPauliBasis.sheetIdentity, ChiralStokesPauliBasis.sheetParity,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply] <;> ring

end InfoGeometry.Canonical.HestenesPauliSheetBridge
