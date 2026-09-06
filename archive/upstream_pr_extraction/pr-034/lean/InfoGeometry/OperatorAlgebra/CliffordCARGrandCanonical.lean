import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.CliffordCAR
import InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity

/-!
# Two-sheet grand-canonical operators

The two sheet labels are represented by two CAR modes in `Clnn 2`.  This file
keeps the number and chiral-charge expressions inside the noncommutative
Clifford algebra; only the chemical potentials are real scalars acting on that
operator carrier.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

noncomputable section

abbrev TwoSheetCAR := Clnn 2

def numberPlus : TwoSheetCAR := cre 2 0 * ann 2 0

def numberMinus : TwoSheetCAR := cre 2 1 * ann 2 1

def totalNumber : TwoSheetCAR := numberPlus + numberMinus

def chiralCharge : TwoSheetCAR := numberPlus - numberMinus

def grandGenerator (H : TwoSheetCAR) (μ μχ : ℝ) : TwoSheetCAR :=
  H - μ • totalNumber - μχ • chiralCharge

theorem totalNumber_eq_numberPlus_add_numberMinus :
    totalNumber = numberPlus + numberMinus := rfl

theorem chiralCharge_eq_numberPlus_sub_numberMinus :
    chiralCharge = numberPlus - numberMinus := rfl

theorem numberPlus_numberMinus_commute :
    numberPlus * numberMinus - numberMinus * numberPlus = 0 := by
  have h := mixedGenerator_commutator_mixedGenerator 2 0 0 1 1
  calc
    numberPlus * numberMinus - numberMinus * numberPlus =
        mixedGenerator 2 0 0 * mixedGenerator 2 1 1 -
          mixedGenerator 2 1 1 * mixedGenerator 2 0 0 := by
      unfold mixedGenerator
      apply InfoGeometry.OperatorAlgebra.commutator_sub_central
      intro z
      simpa [Algebra.smul_def] using
        (Algebra.commutes (R := ℝ) (A := TwoSheetCAR) (1 / 2 : ℝ) z)
    _ = 0 := by
      norm_num at h
      exact h

theorem totalNumber_chiralCharge_commute :
    totalNumber * chiralCharge - chiralCharge * totalNumber = 0 := by
  unfold totalNumber chiralCharge
  have hEq : numberMinus * numberPlus = numberPlus * numberMinus := by
    have h := congrArg Neg.neg numberPlus_numberMinus_commute
    have hrev : numberMinus * numberPlus - numberPlus * numberMinus = 0 := by
      simpa [sub_eq_add_neg] using h
    exact sub_eq_zero.mp hrev
  calc
    (numberPlus + numberMinus) * (numberPlus - numberMinus) -
          (numberPlus - numberMinus) * (numberPlus + numberMinus) =
        0 := by
      simp only [add_mul, mul_add, sub_mul, mul_sub]
      rw [hEq]
      noncomm_ring

theorem chemical_potential_decomposition (μ μχ : ℝ) :
    (μ + μχ) • numberPlus + (μ - μχ) • numberMinus =
      μ • totalNumber + μχ • chiralCharge := by
  simp only [totalNumber, chiralCharge, add_smul, sub_smul]
  module

theorem grandGenerator_sheet_form (H : TwoSheetCAR) (μ μχ : ℝ) :
    grandGenerator H μ μχ =
      H - (μ + μχ) • numberPlus - (μ - μχ) • numberMinus := by
  unfold grandGenerator
  calc
    H - μ • totalNumber - μχ • chiralCharge =
        H - (μ • totalNumber + μχ • chiralCharge) := by noncomm_ring
    _ = H - ((μ + μχ) • numberPlus + (μ - μχ) • numberMinus) := by
      rw [chemical_potential_decomposition]
    _ = H - (μ + μχ) • numberPlus - (μ - μχ) • numberMinus := by
      noncomm_ring

/-!
The chiral chemical-potential term is compatible with an equilibrium
Hamiltonian only when the corresponding charge is conserved.  The following
is the operator statement; no state, trace, or analytic flow is involved.
-/
theorem grandGenerator_chiralCharge_commute_of_hamiltonian_commutes
    (H : TwoSheetCAR)
    (μ μχ : ℝ)
    (hH : H * chiralCharge - chiralCharge * H = 0) :
    grandGenerator H μ μχ * chiralCharge -
        chiralCharge * grandGenerator H μ μχ = 0 := by
  unfold grandGenerator
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  have hN : totalNumber * chiralCharge - chiralCharge * totalNumber = 0 :=
    totalNumber_chiralCharge_commute
  calc
    H * chiralCharge - μ • (totalNumber * chiralCharge) -
          μχ • (chiralCharge * chiralCharge) -
          (chiralCharge * H - μ • (chiralCharge * totalNumber) -
            μχ • (chiralCharge * chiralCharge)) =
        (H * chiralCharge - chiralCharge * H) -
          μ • (totalNumber * chiralCharge - chiralCharge * totalNumber) -
          μχ • (chiralCharge * chiralCharge - chiralCharge * chiralCharge) := by
            module
    _ = 0 := by rw [hH, hN]; simp

end

end InfoGeometry.OperatorAlgebra.CliffordCAR
