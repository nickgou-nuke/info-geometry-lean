import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

open scoped Matrix

/-!
# Mixed-order associative generalized Clifford relations

The sheet factor has order two and the colour factor has order three. This
owner proves their mixed generalized-Clifford presentation on the existing
associative matrix carrier `Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ`.

The homogeneous order-six pair uses
`X₆ = J ⊗ X` and `Z₆ = Γ ⊗ Z²`; its phase is `-ω²`. This file makes no
identification with the repository's separate alternative split-octonion
product.
-/

namespace InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra

abbrev SheetMatrix := TwoSheetThreeColorWeyl.Mat2C
abbrev ColourMatrix := TwoSheetThreeColorWeyl.Mat3C
abbrev SixMatrix := TwoSheetThreeColorWeyl.Mat23C

open TwoSheetThreeColorWeyl

noncomputable section

theorem sixMatrix_finrank : Module.finrank ℂ SixMatrix = 36 := by
  simp [SixMatrix, Module.finrank_matrix]

/-- The missing order-two Clifford relation `ΓJ = -JΓ`; the two square
relations remain owned by `sheetParity_sq` and `sheetExchange_sq`. -/
theorem sheetParity_mul_sheetExchange :
    sheetParity * sheetExchange = -(sheetExchange * sheetParity) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sheetParity, sheetExchange, uPlus, uMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Sheet parity commutes with the colour shift on the separate tensor factor. -/
theorem sixParity_commute_sixShift : Commute sixParity sixShift := by
  change sixParity * sixShift = sixShift * sixParity
  rw [sixParity, sixShift, kronecker_mul, kronecker_mul]
  simp

/-- Sheet exchange commutes with the colour shift. -/
theorem sixSheetExchange_commute_sixShift :
    Commute sixSheetExchange sixShift := by
  change sixSheetExchange * sixShift = sixShift * sixSheetExchange
  rw [sixSheetExchange, sixShift, kronecker_mul, kronecker_mul]
  simp

/-- Sheet parity commutes with every colour clock. -/
theorem sixParity_commute_sixClock (ω : ℂ) :
    Commute sixParity (sixClock ω) := by
  change sixParity * sixClock ω = sixClock ω * sixParity
  rw [sixParity, sixClock, kronecker_mul, kronecker_mul]
  simp

/-- Sheet exchange commutes with every colour clock. -/
theorem sixSheetExchange_commute_sixClock (ω : ℂ) :
    Commute sixSheetExchange (sixClock ω) := by
  change sixSheetExchange * sixClock ω = sixClock ω * sixSheetExchange
  rw [sixSheetExchange, sixClock, kronecker_mul, kronecker_mul]
  simp

/-- The CRT-compatible order-six shift `J ⊗ X`. -/
def sixWeylX : SixMatrix :=
  Matrix.kronecker sheetExchange colorShift

/-- The CRT-compatible order-six clock `Γ ⊗ Z²`. -/
def sixWeylZ (ω : ℂ) : SixMatrix :=
  Matrix.kronecker sheetParity (colorClock ω ^ 2)

/-- The induced sixth-root phase. -/
def sixWeylRoot (ω : ℂ) : ℂ :=
  -(ω ^ 2)

/-- Squaring `X₆` removes the sheet exchange and leaves `I ⊗ X²`. -/
theorem sixWeylX_sq :
    sixWeylX ^ 2 = Matrix.kronecker (1 : SheetMatrix) (colorShift ^ 2) := by
  rw [sixWeylX, kronecker_pow_two]
  simpa [pow_two] using congrArg
    (fun A : SheetMatrix => Matrix.kronecker A (colorShift ^ 2))
    sheetExchange_sq

private theorem sixWeylX_cube :
    sixWeylX ^ 3 = Matrix.kronecker sheetExchange (1 : ColourMatrix) := by
  have hJ3 : sheetExchange ^ 3 = sheetExchange := by
    simp [pow_succ, pow_two, sheetExchange_sq]
  rw [sixWeylX, kronecker_pow_three, hJ3, colorShift_cubed]

/-- The order-six shift has sixth power one. -/
theorem sixWeylX_six : sixWeylX ^ 6 = (1 : SixMatrix) := by
  have hJ2 : sheetExchange ^ 2 = (1 : SheetMatrix) := by
    simpa [pow_two] using sheetExchange_sq
  calc
    sixWeylX ^ 6 = (sixWeylX ^ 3) ^ 2 := by rw [← pow_mul]
    _ = (Matrix.kronecker sheetExchange (1 : ColourMatrix)) ^ 2 := by
      rw [sixWeylX_cube]
    _ = Matrix.kronecker (sheetExchange ^ 2)
        ((1 : ColourMatrix) ^ 2) := by rw [kronecker_pow_two]
    _ = 1 := by rw [hJ2]; simp

private theorem colorClock_pow_six (ω : ℂ) (hω : ω ^ 3 = 1) :
    colorClock ω ^ 6 = (1 : ColourMatrix) := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul,
    colorClock_cubed ω hω]
  simp

/-- Cubing the order-six clock recovers the lifted sheet parity. -/
theorem sixWeylZ_cube (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylZ ω ^ 3 = sixParity := by
  calc
    sixWeylZ ω ^ 3 = Matrix.kronecker (sheetParity ^ 3)
        ((colorClock ω ^ 2) ^ 3) := by
      rw [sixWeylZ, kronecker_pow_three]
    _ = Matrix.kronecker sheetParity (colorClock ω ^ 6) := by
      rw [sheetParity_cube, ← pow_mul]
    _ = Matrix.kronecker sheetParity (1 : ColourMatrix) := by
      rw [colorClock_pow_six ω hω]
    _ = sixParity := rfl

/-- The order-six clock has sixth power one. -/
theorem sixWeylZ_six (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylZ ω ^ 6 = (1 : SixMatrix) := by
  calc
    sixWeylZ ω ^ 6 = (sixWeylZ ω ^ 3) ^ 2 := by rw [← pow_mul]
    _ = sixParity ^ 2 := by rw [sixWeylZ_cube ω hω]
    _ = 1 := sixParity_squared

theorem sixWeylZ_cube_ne_one (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylZ ω ^ 3 ≠ (1 : SixMatrix) := by
  rw [sixWeylZ_cube ω hω]
  intro h
  have hentry := congrArg (fun A : SixMatrix => A (1, 0) (1, 0)) h
  have hzero : (-1 : ℂ) = 1 := by
    simpa [sixParity, sheetParity, uPlus, uMinus,
      Matrix.kroneckerMap_apply] using hentry
  norm_num at hzero

theorem sixWeylZ_sq_ne_one (ω : ℂ) (hω : ω ^ 3 = 1) (hω_ne_one : ω ≠ 1) :
    sixWeylZ ω ^ 2 ≠ (1 : SixMatrix) := by
  intro h
  have h' := h
  rw [pow_two, sixWeylZ, kronecker_mul] at h'
  have hentry := congrArg (fun A : SixMatrix => A (0, 1) (0, 1)) h'
  have hpow' : ω * ω * (ω * ω) = 1 := by
    simpa [sixWeylZ, sheetParity, uPlus, uMinus, colorClock,
      Matrix.kroneckerMap_apply, pow_two] using hentry
  have hpow : ω ^ 4 = 1 := by
    calc
      ω ^ 4 = ω * ω * (ω * ω) := by ring
      _ = 1 := hpow'
  have hzero : ω = 1 := by
    calc
      ω = ω * 1 := by simp
      _ = ω * ω ^ 3 := by rw [hω]
      _ = ω ^ 4 := by ring
      _ = 1 := hpow
  exact hω_ne_one hzero

theorem sixWeylZ_order (ω : ℂ) (hω : ω ^ 3 = 1) (hω_ne_one : ω ≠ 1) :
    orderOf (sixWeylZ ω) = 6 := by
  have hdvd : orderOf (sixWeylZ ω) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one (sixWeylZ_six ω hω)
  have hpos : 0 < orderOf (sixWeylZ ω) := by
    exact (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨6, by norm_num, sixWeylZ_six ω hω⟩).orderOf_pos
  have hle : orderOf (sixWeylZ ω) ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  generalize hk : orderOf (sixWeylZ ω) = k at hdvd hpos hle ⊢
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 := by
    interval_cases k <;> omega
  rcases hk_cases with h | h | h | h
  · have hZ : sixWeylZ ω = 1 := by
      have hord : orderOf (sixWeylZ ω) = 1 := hk.trans h
      simpa only [hord, pow_one] using pow_orderOf_eq_one (sixWeylZ ω)
    exact False.elim (sixWeylZ_cube_ne_one ω hω (by simp [hZ]))
  · have hZ2 : sixWeylZ ω ^ 2 = (1 : SixMatrix) := by
      have hord : orderOf (sixWeylZ ω) = 2 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one (sixWeylZ ω)
    exact False.elim (sixWeylZ_sq_ne_one ω hω hω_ne_one hZ2)
  · have hZ3 : sixWeylZ ω ^ 3 = (1 : SixMatrix) := by
      have hord : orderOf (sixWeylZ ω) = 3 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one (sixWeylZ ω)
    exact False.elim (sixWeylZ_cube_ne_one ω hω hZ3)
  · exact h

/-- Moving the colour shift through two clocks contributes `ω²`. -/
theorem colorClock_sq_mul_shift (ω : ℂ) (hω : ω ^ 3 = 1) :
    colorClock ω ^ 2 * colorShift =
      (ω ^ 2) • (colorShift * colorClock ω ^ 2) := by
  calc
    colorClock ω ^ 2 * colorShift =
        colorClock ω * (colorClock ω * colorShift) := by
      simp [pow_two, mul_assoc]
    _ = colorClock ω * (ω • (colorShift * colorClock ω)) := by
      rw [color_weyl_relation ω hω]
    _ = ω • (colorClock ω * (colorShift * colorClock ω)) := by simp
    _ = ω • ((colorClock ω * colorShift) * colorClock ω) := by
      simp [mul_assoc]
    _ = ω • ((ω • (colorShift * colorClock ω)) * colorClock ω) := by
      rw [color_weyl_relation ω hω]
    _ = (ω ^ 2) • (colorShift * colorClock ω ^ 2) := by
      simp [pow_two, smul_smul, mul_assoc]

/-- The homogeneous relation `Z₆X₆ = (-ω²)X₆Z₆`. -/
theorem sixWeylZ_mul_sixWeylX (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylZ ω * sixWeylX =
      sixWeylRoot ω • (sixWeylX * sixWeylZ ω) := by
  rw [sixWeylZ, sixWeylX, kronecker_mul, kronecker_mul,
    colorClock_sq_mul_shift ω hω, sheetParity_mul_sheetExchange]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [sixWeylRoot, Matrix.kroneckerMap_apply, smul_eq_mul]
  ring

/-! The mixed Weyl relation propagates to every power of the shift. -/

theorem sixWeylZ_mul_sixWeylX_pow (ω : ℂ) (hω : ω ^ 3 = 1) (n : ℕ) :
    sixWeylZ ω * sixWeylX ^ n =
      (sixWeylRoot ω ^ n) • (sixWeylX ^ n * sixWeylZ ω) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc]
      rw [sixWeylZ_mul_sixWeylX ω hω]
      simp [pow_succ, smul_smul, mul_assoc]

/-- The induced phase has sixth power one. -/
theorem sixWeylRoot_six (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylRoot ω ^ 6 = 1 := by
  calc
    sixWeylRoot ω ^ 6 = (ω ^ 3) ^ 4 := by
      simp [sixWeylRoot]
      ring
    _ = 1 := by rw [hω]; simp

theorem sixWeylRoot_cube (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylRoot ω ^ 3 = (-1 : ℂ) := by
  calc
    sixWeylRoot ω ^ 3 = -(ω ^ 6) := by
      simp [sixWeylRoot]
      ring
    _ = -((ω ^ 3) ^ 2) := by ring
    _ = -1 := by rw [hω]; simp

theorem sixWeylRoot_sq_ne_one (ω : ℂ) (hω : ω ^ 3 = 1)
    (hω_ne_one : ω ≠ 1) : sixWeylRoot ω ^ 2 ≠ (1 : ℂ) := by
  intro h
  have hroot : (-ω ^ 2) ^ 2 = 1 := by
    simpa [sixWeylRoot] using h
  have hpow' : ω * ω * (ω * ω) = 1 := by
    simpa [pow_two] using hroot
  have hpow : ω ^ 4 = 1 := by
    calc
      ω ^ 4 = ω * ω * (ω * ω) := by ring
      _ = 1 := hpow'
  have hzero : ω = 1 := by
    calc
      ω = ω * 1 := by simp
      _ = ω * ω ^ 3 := by rw [hω]
      _ = ω ^ 4 := by ring
      _ = 1 := hpow
  exact hω_ne_one hzero

theorem sixWeylRoot_order (ω : ℂ) (hω : ω ^ 3 = 1)
    (hω_ne_one : ω ≠ 1) : orderOf (sixWeylRoot ω) = 6 := by
  have hdvd : orderOf (sixWeylRoot ω) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one (sixWeylRoot_six ω hω)
  have hpos : 0 < orderOf (sixWeylRoot ω) := by
    exact (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨6, by norm_num, sixWeylRoot_six ω hω⟩).orderOf_pos
  have hle : orderOf (sixWeylRoot ω) ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  generalize hk : orderOf (sixWeylRoot ω) = k at hdvd hpos hle ⊢
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 := by
    interval_cases k <;> omega
  rcases hk_cases with h | h | h | h
  · have hroot : sixWeylRoot ω = 1 := by
      have hord : orderOf (sixWeylRoot ω) = 1 := hk.trans h
      simpa only [hord, pow_one] using pow_orderOf_eq_one (sixWeylRoot ω)
    exact False.elim (by
      have hroot_cube := sixWeylRoot_cube ω hω
      rw [hroot] at hroot_cube
      norm_num at hroot_cube)
  · have hroot2 : sixWeylRoot ω ^ 2 = (1 : ℂ) := by
      have hord : orderOf (sixWeylRoot ω) = 2 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one (sixWeylRoot ω)
    exact False.elim (sixWeylRoot_sq_ne_one ω hω hω_ne_one hroot2)
  · have hroot3 : sixWeylRoot ω ^ 3 = (1 : ℂ) := by
      have hord : orderOf (sixWeylRoot ω) = 3 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one (sixWeylRoot ω)
    exact False.elim (by
      have hroot_cube := sixWeylRoot_cube ω hω
      rw [hroot_cube] at hroot3
      norm_num at hroot3)
  · exact h

/-- The fourth power of `X₆` is the lifted colour shift. -/
theorem sixWeylX_four : sixWeylX ^ 4 = sixShift := by
  have hJ2 : sheetExchange ^ 2 = (1 : SheetMatrix) := by
    simpa [pow_two] using sheetExchange_sq
  calc
    sixWeylX ^ 4 = sixWeylX ^ 3 * sixWeylX := by rw [pow_succ]
    _ = Matrix.kronecker sheetExchange (1 : ColourMatrix) *
        Matrix.kronecker sheetExchange colorShift := by
      rw [sixWeylX_cube]
      rfl
    _ = Matrix.kronecker (sheetExchange * sheetExchange)
        ((1 : ColourMatrix) * colorShift) := by rw [kronecker_mul]
    _ = sixShift := by simp [hJ2, sixShift, pow_two]

theorem sixWeylX_four_ne_one : sixWeylX ^ 4 ≠ (1 : SixMatrix) := by
  intro h
  have hentry := congrArg (fun A : SixMatrix => A (0, 0) (0, 2)) h
  rw [sixWeylX_four] at hentry
  have hzero : (0 : ℂ) = 1 := by
    simpa [sixShift, colorShift, Matrix.kroneckerMap_apply] using hentry
  norm_num at hzero

theorem sixWeylX_cube_ne_one : sixWeylX ^ 3 ≠ (1 : SixMatrix) := by
  intro h
  have hentry := congrArg (fun A : SixMatrix => A (0, 0) (1, 0)) h
  rw [sixWeylX_cube] at hentry
  have hzero : (1 : ℂ) = 0 := by
    simpa [sheetExchange, Matrix.kroneckerMap_apply] using hentry
  norm_num at hzero

theorem sixWeylX_order : orderOf sixWeylX = 6 := by
  have hdvd : orderOf sixWeylX ∣ 6 :=
    orderOf_dvd_of_pow_eq_one sixWeylX_six
  have hpos : 0 < orderOf sixWeylX := by
    exact (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨6, by norm_num, sixWeylX_six⟩).orderOf_pos
  have hle : orderOf sixWeylX ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  generalize hk : orderOf sixWeylX = k at hdvd hpos hle ⊢
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 := by
    interval_cases k <;> omega
  rcases hk_cases with h | h | h | h
  · have hX : sixWeylX = 1 := by
      have hord : orderOf sixWeylX = 1 := hk.trans h
      simpa only [hord, pow_one] using pow_orderOf_eq_one sixWeylX
    exact False.elim (sixWeylX_four_ne_one (by simp [hX]))
  · have hX2 : sixWeylX ^ 2 = (1 : SixMatrix) := by
      have hord : orderOf sixWeylX = 2 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one sixWeylX
    have hX4 : sixWeylX ^ 4 = (1 : SixMatrix) := by
      calc
        sixWeylX ^ 4 = (sixWeylX ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hX2]; simp
    exact False.elim (sixWeylX_four_ne_one hX4)
  · have hX3 : sixWeylX ^ 3 = (1 : SixMatrix) := by
      have hord : orderOf sixWeylX = 3 := hk.trans h
      simpa only [hord] using pow_orderOf_eq_one sixWeylX
    exact False.elim (sixWeylX_cube_ne_one hX3)
  · exact h

/-- The certified triality is literally the generalized-Clifford monomial
`X₆⁴ Z₆³`. -/
theorem sixTriality_eq_gca_monomial (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixTriality = sixWeylX ^ 4 * sixWeylZ ω ^ 3 := by
  rw [sixWeylX_four, sixWeylZ_cube ω hω]
  rw [sixShift, sixParity, sixTriality, kronecker_mul]
  simp

end
end InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra
