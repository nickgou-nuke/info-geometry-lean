import InfoGeometry.Lie.SplitOctonionImaginaryEllSupport
import InfoGeometry.Physics.Algebra.LinearTripotentTrifactor

/-!
# Spectral readout of the intrinsic imaginary `ell` operator

This owner exposes only polynomial consequences of the already proved native
tripotence `imaginaryEllT ^ 3 = imaginaryEllT`.  It does not identify the
intrinsic support with the circular Zorn sectors.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryEllSpectralReadout

open InfoGeometry.Lie.SplitOctonionImaginaryEllSupport
open InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization
open InfoGeometry.Physics.Algebra

abbrev Imaginary := InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary
abbrev EndT := Module.End ℝ Imaginary
abbrev T : EndT :=
  InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization.imaginaryEllT

private theorem t_sq_mul_t_sq :
    T * T * (T * T) = T * T := by
  have hT : T * T * T = T := by
    change T ^ 3 = T
    exact imaginaryEllT_tripotent
  calc
    T * T * (T * T) = (T * T * T) * T := by simp only [mul_assoc]
    _ = T * T := by rw [hT]

theorem imaginaryEllT_pow_even (m : ℕ) :
    T ^ (2 * (m + 1)) = T ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, pow_add, ih]
      exact t_sq_mul_t_sq

theorem imaginaryEllT_pow_odd (m : ℕ) :
    T ^ (2 * (m + 1) + 1) = T := by
  rw [pow_succ, imaginaryEllT_pow_even]
  change T ^ 3 = T
  exact imaginaryEllT_tripotent

/-- The three polynomial projectors of the intrinsic tripotent. -/
def imaginaryEllPPlus : EndT := projPos T

def imaginaryEllPZero : EndT := projZero T

def imaginaryEllPMinus : EndT := projNeg T

theorem imaginaryEllPPlus_formula :
    imaginaryEllPPlus = (1 / 2 : ℝ) • (T * T + T) := rfl

theorem imaginaryEllPZero_formula :
    imaginaryEllPZero = 1 - T * T := rfl

theorem imaginaryEllPMinus_formula :
    imaginaryEllPMinus = (1 / 2 : ℝ) • (T * T - T) := rfl

theorem imaginaryEll_projectors_sum :
    imaginaryEllPPlus + imaginaryEllPZero + imaginaryEllPMinus = 1 := by
  exact proj_sum_eq_id (T := T)

theorem imaginaryEllPPlus_sub_PMinus :
    imaginaryEllPPlus - imaginaryEllPMinus = T := by
  exact projPos_sub_projNeg (T := T)

/-- Every imaginary vector splits into the three polynomial spectral
components of the native tripotent. -/
theorem imaginaryEll_projector_decomposition (X : Imaginary) :
    imaginaryEllPPlus X + imaginaryEllPZero X + imaginaryEllPMinus X = X := by
  have h := congrArg (fun A : EndT => A X) imaginaryEll_projectors_sum
  simpa using h

/-- The tripotent acts by the signed difference of its positive and negative
spectral components. -/
theorem imaginaryEllT_apply_decomposition (X : Imaginary) :
    T X = imaginaryEllPPlus X - imaginaryEllPMinus X := by
  have h := congrArg (fun A : EndT => A X) imaginaryEllPPlus_sub_PMinus
  simpa using h.symm

private theorem imaginaryEllT_tripotent_mul : T * T * T = T := by
  change T ^ 3 = T
  exact imaginaryEllT_tripotent

@[simp] theorem imaginaryEllPPlus_idempotent :
    imaginaryEllPPlus * imaginaryEllPPlus = imaginaryEllPPlus := by
  exact projPos_idempotent imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPZero_idempotent :
    imaginaryEllPZero * imaginaryEllPZero = imaginaryEllPZero := by
  exact projZero_idempotent imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPMinus_idempotent :
    imaginaryEllPMinus * imaginaryEllPMinus = imaginaryEllPMinus := by
  exact projNeg_idempotent imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllT_mul_PPlus : T * imaginaryEllPPlus = imaginaryEllPPlus := by
  exact mul_projPos imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllT_mul_PMinus : T * imaginaryEllPMinus = -imaginaryEllPMinus := by
  exact mul_projNeg imaginaryEllT_tripotent_mul

theorem imaginaryEllT_mul_PZero : T * imaginaryEllPZero = 0 := by
  exact mul_projZero imaginaryEllT_tripotent_mul

theorem imaginaryEllPZero_mul_T : imaginaryEllPZero * T = 0 := by
  exact projZero_mul imaginaryEllT_tripotent_mul

/-! The polynomial projectors expose the three pointwise spectral actions. -/
@[simp] theorem imaginaryEllT_apply_PPlus (X : Imaginary) :
    T (imaginaryEllPPlus X) = imaginaryEllPPlus X := by
  have h := congrArg (fun A : EndT => A X) imaginaryEllT_mul_PPlus
  simpa only [Module.End.mul_apply] using h

@[simp] theorem imaginaryEllT_apply_PMinus (X : Imaginary) :
    T (imaginaryEllPMinus X) = -imaginaryEllPMinus X := by
  have h := congrArg (fun A : EndT => A X) imaginaryEllT_mul_PMinus
  simpa only [Module.End.mul_apply] using h

theorem imaginaryEllT_apply_PZero (X : Imaginary) :
    T (imaginaryEllPZero X) = 0 := by
  have h := congrArg (fun A : EndT => A X) imaginaryEllT_mul_PZero
  simpa only [Module.End.mul_apply] using h

@[simp] theorem imaginaryEllPPlus_mul_PMinus :
    imaginaryEllPPlus * imaginaryEllPMinus = 0 := by
  exact projPos_mul_projNeg_eq_zero imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPMinus_mul_PPlus :
    imaginaryEllPMinus * imaginaryEllPPlus = 0 := by
  exact projNeg_mul_projPos_eq_zero imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPPlus_mul_PZero :
    imaginaryEllPPlus * imaginaryEllPZero = 0 := by
  exact projPos_mul_projZero_eq_zero imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPZero_mul_PPlus :
    imaginaryEllPZero * imaginaryEllPPlus = 0 := by
  exact projZero_mul_projPos_eq_zero imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPMinus_mul_PZero :
    imaginaryEllPMinus * imaginaryEllPZero = 0 := by
  exact projNeg_mul_projZero_eq_zero imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPZero_mul_PMinus :
    imaginaryEllPZero * imaginaryEllPMinus = 0 := by
  exact projZero_mul_projNeg_eq_zero imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPPlus_mul_T : imaginaryEllPPlus * T = imaginaryEllPPlus := by
  exact projPos_mul imaginaryEllT_tripotent_mul

@[simp] theorem imaginaryEllPMinus_mul_T : imaginaryEllPMinus * T = -imaginaryEllPMinus := by
  exact projNeg_mul imaginaryEllT_tripotent_mul

theorem imaginaryEllT_sq_eq_PPlus_add_PMinus :
    T * T = imaginaryEllPPlus + imaginaryEllPMinus := by
  have hT : T ^ 3 = T := imaginaryEllT_tripotent
  exact endT_sq_eq_projPos_add_projNeg T hT

/-! The polynomial active projector has exactly the native active support. -/
theorem imaginaryEllPActive_range_eq_support :
    LinearMap.range (imaginaryEllPPlus + imaginaryEllPMinus) = ActiveSupport := by
  rw [← imaginaryEllT_sq_eq_PPlus_add_PMinus]
  rfl

theorem imaginaryEllPZero_range_eq_kernel :
    LinearMap.range imaginaryEllPZero = LinearMap.ker T := by
  have hT : T ^ 3 = T := imaginaryEllT_tripotent
  simpa [imaginaryEllPZero, endProjZero] using
    endProjZero_range_eq_ker T hT

theorem imaginaryEllPPlus_range_eq_eigenspace :
    LinearMap.range imaginaryEllPPlus = Module.End.eigenspace T 1 := by
  have hT : T ^ 3 = T := imaginaryEllT_tripotent
  simpa [imaginaryEllPPlus, endProjPos] using
    endProjPos_range_eq_eigenspace T hT

theorem imaginaryEllPMinus_range_eq_eigenspace :
    LinearMap.range imaginaryEllPMinus = Module.End.eigenspace T (-1) := by
  have hT : T ^ 3 = T := imaginaryEllT_tripotent
  simpa [imaginaryEllPMinus, endProjNeg] using
    endProjNeg_range_eq_eigenspace T hT

end InfoGeometry.Lie.SplitOctonionImaginaryEllSpectralReadout
