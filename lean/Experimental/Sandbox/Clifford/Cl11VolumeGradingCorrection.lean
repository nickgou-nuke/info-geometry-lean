import InfoGeometry.Canonical.Cl11MatrixCliffordBridge

/-!
# Corrected volume grading for the finite real `Cl(1,1)` matrix model

This file fixes the order convention `e₁ = splitL`, `e₂ = splitI` and
`ω = e₁ * e₂`.  In this convention `ω = - splitIL = -eps`.  It is an
involution which anticommutes with both generators.  Its two idempotents are
the opposite of the `eps`-labelled Tomita projectors.  They are algebra
idempotents; the light-cone vectors are separate nilpotent elements.
-/

namespace InfoGeometry.Clifford.Cl11VolumeGradingCorrection

open InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge
open InfoGeometry.Canonical.Cl11MatrixCliffordBridge
open InfoGeometry.Krein.TomitaMatrixAtom
open BottPeriodicityReconciliation
open Matrix

abbrev Carrier := SplitQuaternion

/-- The ordered Clifford volume element `e₁ e₂` for `e₁ = splitL`,
`e₂ = splitI`. -/
def volume : Carrier := splitL * splitI

/-- The `+1` eigenspace idempotent of the ordered volume element. -/
noncomputable def volumePlus : Carrier := (1 / 2 : ℝ) • ((1 : Carrier) + volume)

/-- The `-1` eigenspace idempotent of the ordered volume element. -/
noncomputable def volumeMinus : Carrier := (1 / 2 : ℝ) • ((1 : Carrier) - volume)

theorem volume_eq_neg_splitIL : volume = -splitIL := by
  dsimp [volume, splitIL]
  have hcross : splitL * splitI + splitI * splitL = 0 := by
    simpa [add_comm] using splitI_splitL_anticommute
  exact eq_neg_of_add_eq_zero_left hcross

theorem volume_eq_neg_eps : volume = -eps := by
  rw [volume_eq_neg_splitIL, splitIL_eq_tomita_eps]

theorem volume_sq : volume * volume = (1 : Carrier) := by
  rw [volume_eq_neg_splitIL]
  rw [neg_mul, mul_neg, neg_neg]
  have hOne : splitOne = (1 : Carrier) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitOne, I2]
  rw [← hOne]
  exact splitIL_sq

theorem volume_anticommutes_splitL :
    volume * splitL + splitL * volume = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [volume, splitL, splitI, sigma1, epsilon,
      sigma1R, Matrix.mul_apply, Fin.sum_univ_two]

theorem volume_anticommutes_splitI :
    volume * splitI + splitI * volume = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [volume, splitL, splitI, sigma1, epsilon,
      sigma1R, Matrix.mul_apply, Fin.sum_univ_two]

theorem volumePlus_eq_tomita_Pminus : volumePlus = Pminus := by
  unfold volumePlus
  rw [volume_eq_neg_eps]
  simpa [sub_eq_add_neg] using Pminus_eq_half_one_sub_eps.symm

theorem volumeMinus_eq_tomita_Pplus : volumeMinus = Pplus := by
  unfold volumeMinus
  rw [volume_eq_neg_eps]
  simpa [sub_eq_add_neg] using Pplus_eq_half_one_add_eps.symm

theorem volumePlus_idempotent : volumePlus * volumePlus = volumePlus := by
  rw [volumePlus_eq_tomita_Pminus]
  exact Pminus_idempotent

theorem volumeMinus_idempotent : volumeMinus * volumeMinus = volumeMinus := by
  rw [volumeMinus_eq_tomita_Pplus]
  exact Pplus_idempotent

theorem volume_projectors_orthogonal :
    volumePlus * volumeMinus = 0 ∧ volumeMinus * volumePlus = 0 := by
  rw [volumePlus_eq_tomita_Pminus, volumeMinus_eq_tomita_Pplus]
  exact ⟨Pminus_mul_Pplus, Pplus_mul_Pminus⟩

theorem volume_projectors_resolve_one : volumePlus + volumeMinus = 1 := by
  rw [volumePlus_eq_tomita_Pminus, volumeMinus_eq_tomita_Pplus]
  simpa [add_comm] using Pplus_add_Pminus

/-- With `ω=e₁e₂`, right multiplication by the positive volume idempotent
selects `(e₁+e₂)/2`. -/
theorem splitL_mul_volumePlus :
    splitL * volumePlus = (1 / 2 : ℝ) • (splitL + splitI) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [volumePlus, volume, splitL, splitI, sigma1, epsilon,
      sigma1R, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

/-- The reversed product selects `(e₁-e₂)/2`; left and right multiplication
must not be conflated in this noncommutative algebra. -/
theorem volumePlus_mul_splitL :
    volumePlus * splitL = (1 / 2 : ℝ) • (splitL - splitI) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [volumePlus, volume, splitL, splitI, sigma1, epsilon,
      sigma1R, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply,
      Fin.sum_univ_two]

/-- The two unnormalized null directions have mixed anticommutator `4`. -/
theorem splitNull_opposite_anticommutator :
    splitNull * (splitL - splitI) + (splitL - splitI) * splitNull =
      (4 : ℝ) • (1 : Carrier) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitNull, splitL, splitI, sigma1, epsilon,
      sigma1R, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Fin.sum_univ_two]

/-- Both complementary light-cone directions are square-zero in this matrix
model. -/
theorem lightcone_directions_square_zero :
    splitNull * splitNull = 0 ∧
      (splitL - splitI) * (splitL - splitI) = 0 := by
  exact ⟨splitNull_sq, splitL_sub_splitI_is_nonzero_square_zero.1⟩

/-- Halving both null directions gives a normalized CAR pair. -/
theorem half_null_pair_has_unit_anticommutator :
    ((1 / 2 : ℝ) • splitNull) * ((1 / 2 : ℝ) • (splitL - splitI)) +
      ((1 / 2 : ℝ) • (splitL - splitI)) * ((1 / 2 : ℝ) • splitNull) =
        (1 : Carrier) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitNull, splitL, splitI, sigma1, epsilon,
      sigma1R, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Fin.sum_univ_two]

end InfoGeometry.Clifford.Cl11VolumeGradingCorrection
