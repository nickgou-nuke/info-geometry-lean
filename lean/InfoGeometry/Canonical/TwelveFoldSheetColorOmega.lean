import InfoGeometry.Canonical.KleinBottleSixfoldCyclotomic

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldSheetColorOmega

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

def omegaChi : Mat2C :=
  TwoSheetThreeColorWeyl.uPlus + Complex.I • TwoSheetThreeColorWeyl.uMinus

theorem omegaChi_sq :
    omegaChi * omegaChi = TwoSheetThreeColorWeyl.sheetParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omegaChi, TwoSheetThreeColorWeyl.uPlus,
      TwoSheetThreeColorWeyl.uMinus, TwoSheetThreeColorWeyl.sheetParity,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem omegaChi_four : omegaChi ^ 4 = (1 : Mat2C) := by
  calc
    omegaChi ^ 4 = (omegaChi ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    _ = TwoSheetThreeColorWeyl.sheetParity *
        TwoSheetThreeColorWeyl.sheetParity := by
      have hω2 : omegaChi ^ 2 = TwoSheetThreeColorWeyl.sheetParity := by
        simpa [pow_two] using omegaChi_sq
      rw [hω2]
      simp [pow_two]
    _ = 1 := TwoSheetThreeColorWeyl.sheetParity_sq

theorem sheetParity_ne_one :
    TwoSheetThreeColorWeyl.sheetParity ≠ (1 : Mat2C) := by
  intro h
  have h11 := congrArg (fun M : Mat2C => M 1 1) h
  norm_num [TwoSheetThreeColorWeyl.sheetParity,
    TwoSheetThreeColorWeyl.uPlus, TwoSheetThreeColorWeyl.uMinus] at h11

theorem omegaChi_sq_ne_one : omegaChi ^ 2 ≠ (1 : Mat2C) := by
  have hsq : omegaChi ^ 2 = TwoSheetThreeColorWeyl.sheetParity := by
    simpa [pow_two] using omegaChi_sq
  rw [hsq]
  exact sheetParity_ne_one

theorem omegaChi_exact_period_four :
    omegaChi ^ 4 = (1 : Mat2C) ∧ omegaChi ^ 2 ≠ (1 : Mat2C) :=
  ⟨omegaChi_four, omegaChi_sq_ne_one⟩

theorem omegaChi_cube : omegaChi ^ 3 = !![(1 : ℂ), 0; 0, -Complex.I] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaChi, TwoSheetThreeColorWeyl.uPlus,
      TwoSheetThreeColorWeyl.uMinus, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem omegaChi_sigmaPlus_cube_conjugation :
    omegaChi * TwoSheetThreeColorWeyl.sigmaPlus * omegaChi ^ 3 =
      (-Complex.I : ℂ) • TwoSheetThreeColorWeyl.sigmaPlus := by
  rw [omegaChi_cube]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaChi, TwoSheetThreeColorWeyl.uPlus,
      TwoSheetThreeColorWeyl.uMinus, TwoSheetThreeColorWeyl.sigmaPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

theorem omegaChi_sigmaMinus_cube_conjugation :
    omegaChi * TwoSheetThreeColorWeyl.sigmaMinus * omegaChi ^ 3 =
      (Complex.I : ℂ) • TwoSheetThreeColorWeyl.sigmaMinus := by
  rw [omegaChi_cube]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaChi, TwoSheetThreeColorWeyl.uPlus,
      TwoSheetThreeColorWeyl.uMinus, TwoSheetThreeColorWeyl.sigmaMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

def omegaHat : Mat23C := Matrix.kronecker omegaChi (1 : Mat3C)

def colourHat : Mat23C := Matrix.kronecker (1 : Mat2C) colorShift

def masterTwelve : Mat23C := omegaHat ^ 3 * colourHat ^ 2

theorem masterTwelve_eq_kronecker :
    masterTwelve =
      Matrix.kronecker (omegaChi ^ 3) (colorShift ^ 2) := by
  simp only [masterTwelve, omegaHat, colourHat]
  rw [kronecker_pow_three, kronecker_pow_two, kronecker_mul]
  simp

theorem pow_four_period (a : Mat2C) (ha : a ^ 4 = 1) (k r : ℕ) :
    a ^ (4 * k + r) = a ^ r := by
  rw [pow_add, pow_mul, ha]
  simp

theorem pow_three_period (a : Mat3C) (ha : a ^ 3 = 1) (k r : ℕ) :
    a ^ (3 * k + r) = a ^ r := by
  rw [pow_add, pow_mul, ha]
  simp

theorem masterTwelve_sq :
    masterTwelve ^ 2 = sixTriality := by
  rw [masterTwelve_eq_kronecker, kronecker_pow_two]
  have hω : (omegaChi ^ 3) ^ 2 = omegaChi ^ 6 := by
    rw [← pow_mul]
  have hX : (colorShift ^ 2) ^ 2 = colorShift ^ 4 := by
    rw [← pow_mul]
  rw [hω, hX]
  have hω2 : omegaChi ^ 2 = TwoSheetThreeColorWeyl.sheetParity := by
    simpa [pow_two] using omegaChi_sq
  have hω6 : omegaChi ^ 6 = omegaChi ^ 2 := by
    simpa using pow_four_period omegaChi omegaChi_four 1 2
  have hX4 : colorShift ^ 4 = colorShift := by
    simpa using pow_three_period colorShift colorShift_cubed 1 1
  rw [hω6, hω2, hX4]
  rfl

theorem masterTwelve_cube :
    masterTwelve ^ 3 = omegaHat := by
  rw [masterTwelve_eq_kronecker, kronecker_pow_three]
  have hω : (omegaChi ^ 3) ^ 3 = omegaChi ^ 9 := by
    rw [← pow_mul]
  have hX : (colorShift ^ 2) ^ 3 = colorShift ^ 6 := by
    rw [← pow_mul]
  rw [hω, hX]
  have hω9 : omegaChi ^ 9 = omegaChi := by
    simpa using pow_four_period omegaChi omegaChi_four 2 1
  have hX6 : colorShift ^ 6 = 1 := by
    simpa using pow_three_period colorShift colorShift_cubed 2 0
  rw [hω9, hX6]
  simp [omegaHat]

theorem masterTwelve_six :
    masterTwelve ^ 6 = sixParity := by
  calc
    masterTwelve ^ 6 = (masterTwelve ^ 3) ^ 2 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
    _ = omegaHat ^ 2 := by rw [masterTwelve_cube]
    _ = Matrix.kronecker (omegaChi ^ 2) (1 : Mat3C) := by
      simpa [omegaHat] using kronecker_pow_two omegaChi (1 : Mat3C)
    _ = sixParity := by
      have hω2 : omegaChi ^ 2 = TwoSheetThreeColorWeyl.sheetParity := by
        simpa [pow_two] using omegaChi_sq
      rw [hω2]
      rfl

theorem masterTwelve_eight :
    masterTwelve ^ 8 = colourHat := by
  calc
    masterTwelve ^ 8 = masterTwelve ^ 6 * masterTwelve ^ 2 := by
      rw [← pow_add]
    _ = sixParity * sixTriality := by
      rw [masterTwelve_six, masterTwelve_sq]
    _ = colourHat := by
      change
        Matrix.kronecker TwoSheetThreeColorWeyl.sheetParity (1 : Mat3C) *
            Matrix.kronecker TwoSheetThreeColorWeyl.sheetParity colorShift =
          Matrix.kronecker (1 : Mat2C) colorShift
      rw [kronecker_mul]
      simp [TwoSheetThreeColorWeyl.sheetParity_sq]

theorem masterTwelve_twelve :
    masterTwelve ^ 12 = (1 : Mat23C) := by
  calc
    masterTwelve ^ 12 = (masterTwelve ^ 6) ^ 2 := by
      rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul]
    _ = sixParity ^ 2 := by rw [masterTwelve_six]
    _ = 1 := sixParity_squared

theorem colorShift_ne_one : colorShift ≠ (1 : Mat3C) := by
  intro h
  have h00 := congrArg (fun M : Mat3C => M 0 0) h
  norm_num [colorShift] at h00

theorem sixTriality_ne_one : sixTriality ≠ (1 : Mat23C) := by
  intro h
  have h00 := congrArg (fun M : Mat23C => M (0, 0) (0, 0)) h
  norm_num [sixTriality, Matrix.kroneckerMap_apply, colorShift] at h00

theorem omegaHat_ne_one : omegaHat ≠ (1 : Mat23C) := by
  intro h
  have h11 := congrArg (fun M : Mat23C => M (1, 0) (1, 0)) h
  have hi : Complex.I ≠ (1 : ℂ) := by
    intro hi
    have hre := congrArg Complex.re hi
    norm_num at hre
  dsimp [omegaHat, omegaChi, TwoSheetThreeColorWeyl.uPlus,
    TwoSheetThreeColorWeyl.uMinus, Matrix.kroneckerMap_apply] at h11
  apply hi
  simpa using h11

theorem sixParity_ne_one : sixParity ≠ (1 : Mat23C) := by
  intro h
  have h11 := congrArg (fun M : Mat23C => M (1, 0) (1, 0)) h
  dsimp [sixParity, TwoSheetThreeColorWeyl.sheetParity,
    TwoSheetThreeColorWeyl.uPlus, TwoSheetThreeColorWeyl.uMinus,
    Matrix.kroneckerMap_apply] at h11
  norm_num at h11

theorem colourHat_ne_one : colourHat ≠ (1 : Mat23C) := by
  intro h
  have h00 := congrArg (fun M : Mat23C => M (0, 0) (0, 0)) h
  dsimp [colourHat, colorShift, Matrix.kroneckerMap_apply] at h00
  norm_num at h00

theorem colorShift_sq_explicit :
    colorShift ^ 2 = !![(0 : ℂ), 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pow_two, colorShift, Matrix.mul_apply, Fin.sum_univ_three]

theorem kronecker_colorShift_sq_ne_one :
    Matrix.kronecker (1 : Mat2C) (colorShift ^ 2) ≠ (1 : Mat23C) := by
  intro h
  have h01 := congrArg (fun M : Mat23C => M (0, 0) (0, 1)) h
  rw [colorShift_sq_explicit] at h01
  norm_num [Matrix.kroneckerMap_apply] at h01

theorem sixTriality_sq_ne_one : sixTriality ^ 2 ≠ (1 : Mat23C) := by
  intro h
  have hpow : sixTriality ^ 2 =
      Matrix.kronecker (1 : Mat2C) (colorShift ^ 2) := by
    calc
      sixTriality ^ 2 =
          Matrix.kronecker (TwoSheetThreeColorWeyl.sheetParity ^ 2)
            (colorShift ^ 2) := by
        simpa [sixTriality] using
          kronecker_pow_two TwoSheetThreeColorWeyl.sheetParity colorShift
      _ = Matrix.kronecker (1 : Mat2C) (colorShift ^ 2) := by
        have hparity : TwoSheetThreeColorWeyl.sheetParity ^ 2 =
            (1 : Mat2C) := by
          simpa [pow_two] using TwoSheetThreeColorWeyl.sheetParity_sq
        rw [hparity]
  rw [hpow] at h
  exact kronecker_colorShift_sq_ne_one h

theorem masterTwelve_ne_one : masterTwelve ≠ (1 : Mat23C) := by
  intro h
  apply sixTriality_ne_one
  rw [← masterTwelve_sq, h]
  simp

theorem masterTwelve_pow_two_ne_one :
    masterTwelve ^ 2 ≠ (1 : Mat23C) := by
  simpa [masterTwelve_sq] using sixTriality_ne_one

theorem masterTwelve_pow_three_ne_one :
    masterTwelve ^ 3 ≠ (1 : Mat23C) := by
  simpa [masterTwelve_cube] using omegaHat_ne_one

theorem masterTwelve_pow_four_ne_one :
    masterTwelve ^ 4 ≠ (1 : Mat23C) := by
  intro h
  apply sixTriality_sq_ne_one
  rw [← masterTwelve_sq]
  have hpow : masterTwelve ^ 4 = (masterTwelve ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  rw [← hpow, h]

theorem masterTwelve_pow_six_ne_one :
    masterTwelve ^ 6 ≠ (1 : Mat23C) := by
  simpa [masterTwelve_six] using sixParity_ne_one

theorem masterTwelve_pow_eight_ne_one :
    masterTwelve ^ 8 ≠ (1 : Mat23C) := by
  simpa [masterTwelve_eight] using colourHat_ne_one

theorem masterTwelve_pow_five_ne_one :
    masterTwelve ^ 5 ≠ (1 : Mat23C) := by
  intro h
  have hw : masterTwelve = sixParity := by
    calc
      masterTwelve = masterTwelve ^ 6 := by
        have hpow : masterTwelve ^ 6 = masterTwelve ^ 5 * masterTwelve := by
          calc
            masterTwelve ^ 6 = masterTwelve ^ (5 + 1) := by norm_num
            _ = masterTwelve ^ 5 * masterTwelve := by rw [pow_succ]
        rw [hpow]
        rw [h]
        simp
      _ = sixParity := masterTwelve_six
  apply sixTriality_ne_one
  rw [← masterTwelve_sq, hw]
  simp [sixParity_squared]

theorem masterTwelve_order : orderOf masterTwelve = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · exact masterTwelve_twelve
  intro m hm hm_lt
  interval_cases m
  · simpa [pow_one] using masterTwelve_ne_one
  · exact masterTwelve_pow_two_ne_one
  · exact masterTwelve_pow_three_ne_one
  · exact masterTwelve_pow_four_ne_one
  · exact masterTwelve_pow_five_ne_one
  · exact masterTwelve_pow_six_ne_one
  · intro h
    apply masterTwelve_pow_five_ne_one
    calc
      masterTwelve ^ 5 = masterTwelve ^ 12 := by
        rw [show (12 : ℕ) = 7 + 5 by norm_num, pow_add]
        rw [h]
        simp
      _ = 1 := masterTwelve_twelve
  · exact masterTwelve_pow_eight_ne_one
  · intro h
    apply masterTwelve_pow_three_ne_one
    calc
      masterTwelve ^ 3 = masterTwelve ^ 12 := by
        rw [show (12 : ℕ) = 9 + 3 by norm_num, pow_add]
        rw [h]
        simp
      _ = 1 := masterTwelve_twelve
  · intro h
    apply masterTwelve_pow_two_ne_one
    calc
      masterTwelve ^ 2 = masterTwelve ^ 12 := by
        rw [show (12 : ℕ) = 10 + 2 by norm_num, pow_add]
        rw [h]
        simp
      _ = 1 := masterTwelve_twelve
  · intro h
    apply masterTwelve_ne_one
    calc
      masterTwelve = masterTwelve ^ 12 := by
        rw [show (12 : ℕ) = 11 + 1 by norm_num, pow_add]
        rw [h]
        simp
      _ = 1 := masterTwelve_twelve

end InfoGeometry.Canonical.TwelveFoldSheetColorOmega
