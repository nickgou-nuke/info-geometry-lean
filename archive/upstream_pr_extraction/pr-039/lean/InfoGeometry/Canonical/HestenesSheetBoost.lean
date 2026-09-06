import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Canonical.HestenesOmegaHyperbolic

/-!
# The explicit hyperbolic sheet rotor

The diagonal sheet action is specialized to reciprocal exponential weights.
The resulting conjugation laws are the finite matrix form of the two-sheet
boost factors; no analytic flow or physical interpretation is added here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesSheetBoost

open InfoGeometry.Canonical.HestenesOmegaHyperbolic
open InfoGeometry.Canonical.ChiralStokesPauliBasis

def sheetBoost (η : ℝ) : HestenesOmegaHyperbolic.SheetMatrix :=
  sheetDiagonal (Real.exp (η / 2) : ℂ) (Real.exp (-η / 2) : ℂ)

def sheetBoostInverse (η : ℝ) : HestenesOmegaHyperbolic.SheetMatrix :=
  sheetDiagonal (Real.exp (-η / 2) : ℂ) (Real.exp (η / 2) : ℂ)

theorem sheetBoost_inverse_mul (η : ℝ) :
    sheetBoostInverse η * sheetBoost η =
      (1 : HestenesOmegaHyperbolic.SheetMatrix) := by
  have ha : (Real.exp (η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (η / 2)
  have hb : (Real.exp (-η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (-η / 2)
  unfold sheetBoostInverse sheetBoost
  rw [sheetDiagonal_mul]
  have h₁ : (Real.exp (-η / 2) : ℂ) * Real.exp (η / 2) = 1 := by
    have h : Real.exp (-η / 2) * Real.exp (η / 2) = (1 : ℝ) := by
      rw [← Real.exp_add]
      have hz : -η / 2 + η / 2 = (0 : ℝ) := by ring
      rw [hz, Real.exp_zero]
    exact_mod_cast h
  have h₂ : (Real.exp (η / 2) : ℂ) * Real.exp (-η / 2) = 1 := by
    simpa [mul_comm] using h₁
  rw [h₁, h₂]
  have hone : sheetIdentity = (1 : HestenesOmegaHyperbolic.SheetMatrix) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sheetIdentity]
  calc
    sheetDiagonal (1 : ℂ) 1 = sheetIdentity := sheetDiagonal_one
    _ = (1 : HestenesOmegaHyperbolic.SheetMatrix) := hone

theorem sheetBoost_mul_inverse (η : ℝ) :
    sheetBoost η * sheetBoostInverse η =
      (1 : HestenesOmegaHyperbolic.SheetMatrix) := by
  have ha : (Real.exp (η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (η / 2)
  have hb : (Real.exp (-η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (-η / 2)
  unfold sheetBoost sheetBoostInverse
  rw [sheetDiagonal_mul]
  have h₁ : (Real.exp (η / 2) : ℂ) * Real.exp (-η / 2) = 1 := by
    have h : Real.exp (η / 2) * Real.exp (-η / 2) = (1 : ℝ) := by
      rw [← Real.exp_add]
      have hz : η / 2 + -η / 2 = (0 : ℝ) := by ring
      rw [hz, Real.exp_zero]
    exact_mod_cast h
  have h₂ : (Real.exp (-η / 2) : ℂ) * Real.exp (η / 2) = 1 := by
    simpa [mul_comm] using h₁
  rw [h₁, h₂]
  have hone : sheetIdentity = (1 : HestenesOmegaHyperbolic.SheetMatrix) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sheetIdentity]
  calc
    sheetDiagonal (1 : ℂ) 1 = sheetIdentity := sheetDiagonal_one
    _ = (1 : HestenesOmegaHyperbolic.SheetMatrix) := hone

theorem sheetBoost_conjugates_cPlus (η : ℝ) :
    sheetBoost η * cPlus * sheetBoostInverse η =
      Real.exp η • cPlus := by
  unfold sheetBoost
  have ha : (Real.exp (η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (η / 2)
  have hb : (Real.exp (-η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (-η / 2)
  have hAreal : Real.exp (-η / 2) = (Real.exp (η / 2))⁻¹ := by
    rw [show -η / 2 = -(η / 2) by ring, Real.exp_neg]
  have hA : (Real.exp (-η / 2) : ℂ) =
      (Real.exp (η / 2) : ℂ)⁻¹ := by
    exact_mod_cast hAreal
  have hBreal : Real.exp (η / 2) = (Real.exp (-η / 2))⁻¹ := by
    rw [show -η / 2 = -(η / 2) by ring, Real.exp_neg, inv_inv]
  have hB : (Real.exp (η / 2) : ℂ) =
      (Real.exp (-η / 2) : ℂ)⁻¹ := by
    exact_mod_cast hBreal
  have hInv : sheetBoostInverse η =
      sheetDiagonal (Real.exp (η / 2) : ℂ)⁻¹
        (Real.exp (-η / 2) : ℂ)⁻¹ := by
    unfold sheetBoostInverse
    exact congrArg₂ sheetDiagonal hA hB
  rw [hInv]
  rw [sheetDiagonal_conjugates_cPlus _ _ ha hb]
  have hratio :
      (Real.exp (η / 2) : ℂ) * (Real.exp (-η / 2) : ℂ)⁻¹ =
        (Real.exp η : ℂ) := by
    have h : Real.exp (η / 2) * (Real.exp (-η / 2))⁻¹ = Real.exp η := by
      rw [show -η / 2 = -(η / 2) by ring, Real.exp_neg, inv_inv]
      rw [← Real.exp_add]
      congr 1
      ring
    exact_mod_cast h
  rw [hratio]
  rfl

theorem sheetBoost_conjugates_cMinus (η : ℝ) :
    sheetBoost η * cMinus * sheetBoostInverse η =
      Real.exp (-η) • cMinus := by
  unfold sheetBoost
  have ha : (Real.exp (η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (η / 2)
  have hb : (Real.exp (-η / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (-η / 2)
  have hAreal : Real.exp (-η / 2) = (Real.exp (η / 2))⁻¹ := by
    rw [show -η / 2 = -(η / 2) by ring, Real.exp_neg]
  have hA : (Real.exp (-η / 2) : ℂ) =
      (Real.exp (η / 2) : ℂ)⁻¹ := by
    exact_mod_cast hAreal
  have hBreal : Real.exp (η / 2) = (Real.exp (-η / 2))⁻¹ := by
    rw [show -η / 2 = -(η / 2) by ring, Real.exp_neg, inv_inv]
  have hB : (Real.exp (η / 2) : ℂ) =
      (Real.exp (-η / 2) : ℂ)⁻¹ := by
    exact_mod_cast hBreal
  have hInv : sheetBoostInverse η =
      sheetDiagonal (Real.exp (η / 2) : ℂ)⁻¹
        (Real.exp (-η / 2) : ℂ)⁻¹ := by
    unfold sheetBoostInverse
    exact congrArg₂ sheetDiagonal hA hB
  rw [hInv]
  rw [sheetDiagonal_conjugates_cMinus _ _ ha hb]
  have hratio :
      (Real.exp (-η / 2) : ℂ) * (Real.exp (η / 2) : ℂ)⁻¹ =
        (Real.exp (-η) : ℂ) := by
    have h : Real.exp (-η / 2) * (Real.exp (η / 2))⁻¹ = Real.exp (-η) := by
      calc
        Real.exp (-η / 2) * (Real.exp (η / 2))⁻¹ =
            Real.exp (-η / 2) * Real.exp (-(η / 2)) := by
              rw [Real.exp_neg]
        _ = Real.exp (-η / 2 + -(η / 2)) := by
              rw [← Real.exp_add]
        _ = Real.exp (-η) := by congr 1 <;> ring
    exact_mod_cast h
  rw [hratio]
  rfl

end InfoGeometry.Canonical.HestenesSheetBoost
