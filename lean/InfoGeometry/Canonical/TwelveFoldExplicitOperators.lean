import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Kronecker
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Canonical.SixStateSpectralBridge

open scoped Matrix

namespace InfoGeometry.Canonical.TwelveFoldExplicitOperators

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Canonical.SixStateSpectralBridge

noncomputable section

abbrev Mat2C := TwoSheetThreeColorWeyl.Mat2C
abbrev Mat3C := TwoSheetThreeColorWeyl.Mat3C
abbrev Mat23C := TwoSheetThreeColorWeyl.Mat23C

def omegaChi : Mat2C :=
  uPlus + Complex.I • uMinus

theorem omegaChi_sq : omegaChi ^ 2 = sheetParity := by
  rw [pow_two]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaChi, uPlus, uMinus, sheetParity,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring

theorem omegaChi_four : omegaChi ^ 4 = (1 : Mat2C) := by
  calc
    omegaChi ^ 4 = (omegaChi ^ 2) ^ 2 := by
      rw [← pow_mul]
    _ = sheetParity ^ 2 := by rw [omegaChi_sq]
    _ = 1 := by simpa [pow_two] using sheetParity_sq

def omegaHat : Mat23C :=
  Matrix.kronecker omegaChi (1 : Mat3C)

theorem omegaHat_sq : omegaHat ^ 2 = sixParity := by
  calc
    omegaHat ^ 2 = Matrix.kronecker (omegaChi ^ 2) ((1 : Mat3C) ^ 2) :=
      kronecker_pow_two omegaChi (1 : Mat3C)
    _ = sixParity := by rw [omegaChi_sq]; simp [sixParity]

theorem omegaHat_four : omegaHat ^ 4 = (1 : Mat23C) := by
  calc
    omegaHat ^ 4 = (omegaHat ^ 2) ^ 2 := by rw [← pow_mul]
    _ = sixParity ^ 2 := by rw [omegaHat_sq]
    _ = 1 := by simpa [pow_two] using sixParity_squared

def masterTwelve : Mat23C :=
  omegaHat ^ 3 * sixShift ^ 2

theorem omegaHat_mul_sixShift :
    omegaHat * sixShift = sixShift * omegaHat := by
  rw [omegaHat, sixShift, kronecker_mul, kronecker_mul]
  simp [mul_comm]

theorem masterTwelve_eq_kronecker :
    masterTwelve = Matrix.kronecker (omegaChi ^ 3) (colorShift ^ 2) := by
  rw [masterTwelve, omegaHat, sixShift, kronecker_pow_three,
    kronecker_pow_two, kronecker_mul]
  simp

theorem masterTwelve_sq : masterTwelve ^ 2 = sixTriality := by
  rw [masterTwelve_eq_kronecker, kronecker_pow_two]
  have hω6 : omegaChi ^ 6 = sheetParity := by
    calc
      omegaChi ^ 6 = omegaChi ^ (4 + 2) := by norm_num
      _ = (omegaChi ^ 4) * omegaChi ^ 2 := by rw [pow_add]
      _ = sheetParity := by rw [omegaChi_four, one_mul, omegaChi_sq]
  have hX4 : colorShift ^ 4 = colorShift := by
    calc
      colorShift ^ 4 = colorShift ^ (3 + 1) := by norm_num
      _ = colorShift ^ 3 * colorShift := by rw [pow_add]; simp
      _ = colorShift := by rw [colorShift_cubed, one_mul]
  rw [← pow_mul, ← pow_mul]
  rw [hω6, hX4]
  rfl

theorem masterTwelve_cube : masterTwelve ^ 3 = omegaHat := by
  rw [masterTwelve_eq_kronecker, kronecker_pow_three]
  have hω9 : omegaChi ^ 9 = omegaChi := by
    calc
      omegaChi ^ 9 = omegaChi ^ (8 + 1) := by norm_num
      _ = omegaChi ^ 8 * omegaChi := by rw [pow_add]; simp
      _ = omegaChi := by
        have hω8 : omegaChi ^ 8 = (1 : Mat2C) := by
          rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, omegaChi_four]
          simp
        rw [hω8, one_mul]
  have hX6 : colorShift ^ 6 = (1 : Mat3C) := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, colorShift_cubed]
    simp
  rw [← pow_mul, ← pow_mul, hω9, hX6]
  rfl

theorem masterTwelve_six : masterTwelve ^ 6 = sixParity := by
  calc
    masterTwelve ^ 6 = (masterTwelve ^ 3) ^ 2 := by
      rw [← pow_mul]
    _ = omegaHat ^ 2 := by rw [masterTwelve_cube]
    _ = sixParity := omegaHat_sq

theorem masterTwelve_eight : masterTwelve ^ 8 = sixShift := by
  calc
    masterTwelve ^ 8 = (masterTwelve ^ 2) ^ 4 := by
      rw [← pow_mul]
    _ = sixTriality ^ 4 := by rw [masterTwelve_sq]
    _ = sixShift := by
      calc
        sixTriality ^ 4 = sixTriality ^ 3 * sixTriality := by
          rw [pow_succ]
        _ = sixParity * sixTriality := by rw [sixTriality_cube]
        _ = sixShift := by
          rw [sixParity, sixTriality, sixShift, kronecker_mul]
          simp [sheetParity_sq]

theorem masterTwelve_twelve : masterTwelve ^ 12 = (1 : Mat23C) := by
  calc
    masterTwelve ^ 12 = (masterTwelve ^ 3) ^ 4 := by
      rw [← pow_mul]
    _ = omegaHat ^ 4 := by rw [masterTwelve_cube]
    _ = 1 := omegaHat_four

theorem masterTwelve_sq_mulVec_spectralVector
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    masterTwelve ^ 2 *ᵥ spectralVector zeta n =
      (if (sheetColorEquiv n).1 = .positive then
          zeta (sheetColorEquiv n).2
       else -zeta (sheetColorEquiv n).2) • spectralVector zeta n := by
  rw [masterTwelve_sq]
  exact spectralVector_triality zeta hzeta n

theorem sixParity_ne_one : sixParity ≠ (1 : Mat23C) := by
  intro h
  have hentry := congrArg (fun A : Mat23C => A (1, 0) (1, 0)) h
  norm_num [sixParity, sheetParity, uPlus, uMinus,
    Matrix.kroneckerMap_apply] at hentry

theorem sixShift_ne_one : sixShift ≠ (1 : Mat23C) := by
  intro h
  have hentry := congrArg (fun A : Mat23C => A (0, 0) (0, 2)) h
  have hzero : (0 : ℂ) = 1 := by
    simpa [sixShift, colorShift, Matrix.kroneckerMap_apply] using hentry
  norm_num at hzero

theorem masterTwelve_order_exact : orderOf masterTwelve = 12 := by
  have hdvd : orderOf masterTwelve ∣ 12 :=
    orderOf_dvd_of_pow_eq_one masterTwelve_twelve
  have hnot6 : masterTwelve ^ 6 ≠ (1 : Mat23C) := by
    rw [masterTwelve_six]
    exact sixParity_ne_one
  have hnot4 : masterTwelve ^ 4 ≠ (1 : Mat23C) := by
    intro h
    have h8 : masterTwelve ^ 8 = (1 : Mat23C) := by
      calc
        masterTwelve ^ 8 = (masterTwelve ^ 4) ^ 2 := by
          rw [← pow_mul]
        _ = 1 := by rw [h]; simp
    rw [masterTwelve_eight] at h8
    exact sixShift_ne_one h8
  have hpos : 0 < orderOf masterTwelve := by
    exact (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨12, by norm_num, masterTwelve_twelve⟩).orderOf_pos
  have hle : orderOf masterTwelve ≤ 12 := Nat.le_of_dvd (by decide) hdvd
  generalize hk : orderOf masterTwelve = k at hdvd hpos hle ⊢
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 12 := by
    interval_cases k <;> omega
  rcases hk_cases with h | h | h | h | h | h
  · have hW : masterTwelve = 1 := by
      have hord : orderOf masterTwelve = 1 := hk.trans h
      simpa only [hord, pow_one] using pow_orderOf_eq_one masterTwelve
    exact False.elim (hnot6 (by simpa [hW]))
  · have hW2 : masterTwelve ^ 2 = (1 : Mat23C) := by
      have hord : orderOf masterTwelve = 2 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one masterTwelve
    have hW6 : masterTwelve ^ 6 = (1 : Mat23C) := by
      calc
        masterTwelve ^ 6 = (masterTwelve ^ 2) ^ 3 := by
          rw [← pow_mul]
        _ = 1 := by rw [hW2]; simp
    exact False.elim (hnot6 hW6)
  · have hW3 : masterTwelve ^ 3 = (1 : Mat23C) := by
      have hord : orderOf masterTwelve = 3 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one masterTwelve
    have hW6 : masterTwelve ^ 6 = (1 : Mat23C) := by
      calc
        masterTwelve ^ 6 = (masterTwelve ^ 3) ^ 2 := by
          rw [← pow_mul]
        _ = 1 := by rw [hW3]; simp
    exact False.elim (hnot6 hW6)
  · have hW4 : masterTwelve ^ 4 = (1 : Mat23C) := by
      have hord : orderOf masterTwelve = 4 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one masterTwelve
    exact False.elim (hnot4 hW4)
  · have hW6 : masterTwelve ^ 6 = (1 : Mat23C) := by
      have hord : orderOf masterTwelve = 6 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one masterTwelve
    exact False.elim (hnot6 hW6)
  · exact h

end

end InfoGeometry.Canonical.TwelveFoldExplicitOperators
