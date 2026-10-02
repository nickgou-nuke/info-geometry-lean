import InfoGeometry.Canonical.SpinorialCore.Algebra

/-!
# The corrected sign in mathlib's native Clifford algebra

The universal theorem is over any commutative ring. The real 2 by 2
matrices are concrete witnesses, not a replacement for the Clifford carrier.
-/

noncomputable section
namespace InfoGeometry.Canonical.SpinorialCore

/-- Native Clifford specialization of the mixed-sign product theorem. -/
theorem clifford_mixed_bivector_square
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (v w : M)
    (hv : Q v = 1) (hw : Q w = -1) (ho : Q.IsOrtho v w) :
    (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) *
      (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) = 1 := by
  apply mixed_bivector_square
  · rw [CliffordAlgebra.ι_sq_scalar, hv, map_one]
  · rw [CliffordAlgebra.ι_sq_scalar, hw, map_neg, map_one]
  · apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using
      CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho ho

namespace RealAtom
open Matrix

def positiveGenerator : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def negativeGenerator : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
def grading : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def rightProjector : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def leftProjector : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
def creation : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def annihilation : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

theorem positive_square : positiveGenerator * positiveGenerator = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveGenerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem negative_square : negativeGenerator * negativeGenerator = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [negativeGenerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem product_is_grading : positiveGenerator * negativeGenerator = grading := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveGenerator, negativeGenerator, grading, Matrix.mul_apply, Fin.sum_univ_two]

theorem grading_square : grading * grading = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, Matrix.mul_apply, Fin.sum_univ_two]

theorem projector_partition : rightProjector + leftProjector = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rightProjector, leftProjector]

theorem projector_orthogonality : rightProjector * leftProjector = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightProjector, leftProjector, Matrix.mul_apply, Fin.sum_univ_two]

theorem projector_from_grading : rightProjector = (1 / 2 : ℝ) • (1 + grading) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rightProjector, grading]

theorem creation_square_zero : creation * creation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [creation, Matrix.mul_apply, Fin.sum_univ_two]

theorem annihilation_square_zero : annihilation * annihilation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [annihilation, Matrix.mul_apply, Fin.sum_univ_two]

theorem mixed_car : annihilation * creation + creation * annihilation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [creation, annihilation, Matrix.mul_apply, Fin.sum_univ_two]

end RealAtom
end InfoGeometry.Canonical.SpinorialCore
