import InfoGeometry.Canonical.ChiralStokesPauliRelations

namespace InfoGeometry.Canonical.ChiralStokesPauliBasis

noncomputable section

def uPlus : SheetMatrix :=
  (1 / 2 : ℂ) • (sheetIdentity + sheetParity)

def uMinus : SheetMatrix :=
  (1 / 2 : ℂ) • (sheetIdentity - sheetParity)

def cPlus : SheetMatrix :=
  (1 / 2 : ℂ) • (sheetFlip + Complex.I • sheetPhase)

def cMinus : SheetMatrix :=
  (1 / 2 : ℂ) • (sheetFlip - Complex.I • sheetPhase)

theorem uPlus_idempotent : uPlus * uPlus = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

theorem uMinus_idempotent : uMinus * uMinus = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

theorem uPlus_mul_uMinus : uPlus * uMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

theorem uMinus_mul_uPlus : uMinus * uPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

theorem uPlus_add_uMinus : uPlus + uMinus = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetIdentity, sheetParity] <;>
      norm_num [div_eq_mul_inv]

theorem uPlus_sub_uMinus : uPlus - uMinus = sheetParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, uMinus, sheetIdentity, sheetParity] <;>
      norm_num [div_eq_mul_inv]

theorem cPlus_sq : cPlus * cPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, sheetFlip, sheetPhase, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_sq] <;> norm_num [div_eq_mul_inv]

theorem cMinus_sq : cMinus * cMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cMinus, sheetFlip, sheetPhase, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_sq] <;> norm_num [div_eq_mul_inv]

theorem cPlus_mul_cMinus : cPlus * cMinus = uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, cMinus, uPlus, sheetIdentity, sheetParity, sheetFlip,
      sheetPhase, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem cMinus_mul_cPlus : cMinus * cPlus = uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, cMinus, uMinus, sheetIdentity, sheetParity, sheetFlip,
      sheetPhase, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem uPlus_mul_cPlus : uPlus * cPlus = cPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, cPlus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem cPlus_mul_uMinus : cPlus * uMinus = cPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, uMinus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem uMinus_mul_cPlus : uMinus * cPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, cPlus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem cPlus_mul_uPlus : cPlus * uPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, uPlus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem uMinus_mul_cMinus : uMinus * cMinus = cMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMinus, cMinus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem cMinus_mul_uPlus : cMinus * uPlus = cMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cMinus, uPlus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem uPlus_mul_cMinus : uPlus * cMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uPlus, cMinus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem cMinus_mul_uMinus : cMinus * uMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cMinus, uMinus, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
      norm_num [div_eq_mul_inv]

theorem cPlus_add_cMinus : cPlus + cMinus = sheetFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, cMinus, sheetFlip, sheetPhase] <;>
      norm_num [div_eq_mul_inv]

theorem cPlus_sub_cMinus : cPlus - cMinus = Complex.I • sheetPhase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cPlus, cMinus, sheetFlip, sheetPhase] <;>
      norm_num [div_eq_mul_inv]

theorem sheetPhase_eq_neg_I_smul_cPlus_sub_cMinus :
    sheetPhase = (-Complex.I) • (cPlus - cMinus) := by
  rw [cPlus_sub_cMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetPhase, Complex.I_sq]

end

end InfoGeometry.Canonical.ChiralStokesPauliBasis
