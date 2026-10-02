import InfoGeometry.Canonical.SpinorialCore.KreinAdjoint

/-! # Exponentiating the finite-dimensional Krein Lie algebra -/

noncomputable section
namespace InfoGeometry.Canonical.SpinorialCore.Krein
open Matrix NormedSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An involution packaged as an actual unit, with its inverse proved. -/
def fundamentalUnit (J : Matrix n n ℂ) (hJ : J * J = 1) : (Matrix n n ℂ)ˣ where
  val := J
  inv := J
  val_inv := hJ
  inv_val := hJ

theorem sharp_exp (J X : Matrix n n ℂ) (hJ : J * J = 1) :
    sharp J (exp X) = exp (sharp J X) := by
  simp only [sharp, NormedSpace.star_exp]
  simpa only [fundamentalUnit] using
    (Matrix.exp_units_conj (fundamentalUnit J hJ) (star X)).symm

/-- A genuine matrix exponential, not a formal symbol with an assumed inverse. -/
theorem exp_isIsometry (J X : Matrix n n ℂ) (hJ : J * J = 1)
    (hX : sharp J X = -X) : IsIsometry J (exp X) := by
  apply (isIsometry_iff_sharp_mul J (exp X) hJ).mpr
  rw [sharp_exp J X hJ, hX]
  have hc : Commute (-X) X := by
    change (-X) * X = X * (-X)
    noncomm_ring
  rw [← Matrix.exp_add_of_commute (-X) X hc, neg_add_cancel, NormedSpace.exp_zero]

theorem sharp_real_smul (J X : Matrix n n ℂ) (t : ℝ) :
    sharp J (t • X) = t • sharp J X := by
  simp [sharp, star_smul]

theorem real_flow_isIsometry (J X : Matrix n n ℂ) (hJ : J * J = 1)
    (hX : sharp J X = -X) (t : ℝ) : IsIsometry J (exp (t • X)) := by
  apply exp_isIsometry J (t • X) hJ
  rw [sharp_real_smul, hX, smul_neg]

namespace SplitTwo

def signature : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def generator : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1 / 2; 1 / 2, 0]

theorem signature_square : signature * signature = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [signature, Matrix.mul_apply, Fin.sum_univ_two]

theorem generator_skew : sharp signature generator = -generator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sharp, signature, generator, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct,
      map_ofNat]

theorem boost_isIsometry (t : ℝ) : IsIsometry signature (exp (t • generator)) :=
  real_flow_isIsometry signature generator signature_square generator_skew t

end SplitTwo
end InfoGeometry.Canonical.SpinorialCore.Krein
