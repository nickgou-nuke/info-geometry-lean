import Mathlib.Tactic
import InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra
import InfoGeometry.Canonical.KleinBottleSixfoldCyclotomic

open scoped Matrix

namespace InfoGeometry.Canonical.SixStateWeylReflection

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.KleinBottleSixfoldCyclotomic
open InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra

noncomputable section

abbrev SixMatrix := SixStateGeneralizedCliffordAlgebra.SixMatrix

/-- The concrete sheet-colour reflection on the six-state carrier. -/
def thetaSix : SixMatrix :=
  Matrix.kronecker sheetExchange colorReflection

theorem thetaSix_sq : thetaSix ^ 2 = (1 : SixMatrix) := by
  rw [thetaSix, kronecker_pow_two]
  rw [show sheetExchange ^ 2 = 1 by simp [pow_two, sheetExchange_sq]]
  simp [colorReflection_sq]

theorem thetaSix_ne_one : thetaSix ≠ (1 : SixMatrix) := by
  intro h
  have hentry := congrArg (fun A : SixMatrix => A (0, 0) (1, 0)) h
  have hzero : (1 : ℂ) = 0 := by
    simp [thetaSix, sheetExchange, colorReflection,
      Matrix.kroneckerMap_apply] at hentry
  norm_num at hzero

theorem thetaSix_order : orderOf thetaSix = 2 := by
  have hdvd : orderOf thetaSix ∣ 2 :=
    orderOf_dvd_of_pow_eq_one thetaSix_sq
  have hpos : 0 < orderOf thetaSix := by
    exact (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by norm_num, thetaSix_sq⟩).orderOf_pos
  have hle : orderOf thetaSix ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  generalize hk : orderOf thetaSix = k at hdvd hpos hle ⊢
  have hk_cases : k = 1 ∨ k = 2 := by
    interval_cases k <;> omega
  rcases hk_cases with h | h
  · have htheta : thetaSix = 1 := by
      have hord : orderOf thetaSix = 1 := hk.trans h
      simpa only [hord, pow_one] using pow_orderOf_eq_one thetaSix
    exact False.elim (thetaSix_ne_one htheta)
  · exact h

/-- Reflection sends the homogeneous order-six shift to its inverse. -/
theorem thetaSix_conj_sixWeylX :
    thetaSix * sixWeylX * thetaSix = sixWeylX ^ 5 := by
  calc
    thetaSix * sixWeylX * thetaSix =
        Matrix.kronecker
          (sheetExchange * sheetExchange * sheetExchange)
          (colorReflection * colorShift * colorReflection) := by
      rw [thetaSix, sixWeylX, kronecker_mul, kronecker_mul]
    _ = Matrix.kronecker sheetExchange (colorShift ^ 2) := by
      rw [colorReflection_conjugates_shift]
      simp [sheetExchange_sq]
    _ = sixShift * sixWeylX := by
      rw [sixShift, sixWeylX, kronecker_mul]
      simp [pow_two]
    _ = sixWeylX ^ 5 := by
      rw [← sixWeylX_four, ← pow_succ]

private theorem colorReflection_conj_colorClock_sq (ω : ℂ)
    (hω : ω ^ 3 = 1) :
    colorReflection * (colorClock ω ^ 2) * colorReflection = colorClock ω := by
  have hω4 : ω ^ 4 = ω := by
    calc
      ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [hω]; simp
  have hω4' : ω * ω * (ω * ω) = ω := by
    calc
      ω * ω * (ω * ω) = ω ^ 4 := by ring
      _ = ω := hω4
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [colorReflection, colorClock, Matrix.mul_apply,
    Fin.sum_univ_three, pow_two]
  all_goals exact hω4'

private theorem kronecker_pow (A : SheetMatrix) (B : ColourMatrix) (n : ℕ) :
    (Matrix.kronecker A B) ^ n =
      Matrix.kronecker (A ^ n) (B ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, kronecker_mul, pow_succ]

private theorem sixWeylZ_five (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylZ ω ^ 5 = Matrix.kronecker sheetParity (colorClock ω) := by
  have hP : sheetParity ^ 5 = sheetParity := by
    calc
      sheetParity ^ 5 = sheetParity ^ (2 * 2 + 1) := by norm_num
      _ = sheetParity ^ (2 * 2) * sheetParity := by rw [pow_add]; simp
      _ = sheetParity := by
        simp only [show (2 * 2 : ℕ) = 4 by norm_num]
        have hP4 : sheetParity ^ 4 = (1 : SheetMatrix) := by
          calc
            sheetParity ^ 4 = sheetParity ^ (2 * 2) := by norm_num
            _ = (sheetParity ^ 2) ^ 2 := by rw [pow_mul]
            _ = 1 := by simp [pow_two, sheetParity_sq]
        rw [hP4]
        simp
  have hC : (colorClock ω ^ 2) ^ 5 = colorClock ω := by
    rw [← pow_mul]
    calc
      colorClock ω ^ (2 * 5) = colorClock ω ^ (3 * 3 + 1) := by norm_num
      _ = colorClock ω ^ (3 * 3) * colorClock ω := by rw [pow_add]; simp
      _ = colorClock ω := by
        rw [show colorClock ω ^ (3 * 3) =
          (colorClock ω ^ 3) ^ 3 by rw [pow_mul], colorClock_cubed ω hω]
        simp
  rw [sixWeylZ, kronecker_pow, hP, hC]

/-- The clock normalizer has the central Pin sign: `Θ Z₆ Θ = -Z₆⁻¹`. -/
theorem thetaSix_conj_sixWeylZ (ω : ℂ) (hω : ω ^ 3 = 1) :
    thetaSix * sixWeylZ ω * thetaSix = -(sixWeylZ ω ^ 5) := by
  calc
    thetaSix * sixWeylZ ω * thetaSix =
        Matrix.kronecker
          (sheetExchange * sheetParity * sheetExchange)
          (colorReflection * (colorClock ω ^ 2) * colorReflection) := by
      rw [thetaSix, sixWeylZ, kronecker_mul, kronecker_mul]
    _ = Matrix.kronecker (-sheetParity) (colorClock ω) := by
      rw [sheetExchange_parity_sheetExchange,
        colorReflection_conj_colorClock_sq ω hω]
    _ = -(sixWeylZ ω ^ 5) := by
      rw [sixWeylZ_five ω hω]
      simpa using
        Matrix.smul_kronecker (-1 : ℂ) sheetParity (colorClock ω)

end
end InfoGeometry.Canonical.SixStateWeylReflection
