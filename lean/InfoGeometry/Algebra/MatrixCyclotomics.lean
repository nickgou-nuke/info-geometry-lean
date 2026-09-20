import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.External.Auto.Matrix2KANPauliChain
import InfoGeometry.Geometry.MoebiusChiralGeneratorClassification
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

noncomputable section

namespace InfoGeometry.Algebra.MatrixCyclotomics

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open scoped Matrix

theorem cyclotomic_four (Scalar : Type*) [CommRing Scalar] :
    Polynomial.cyclotomic 4 Scalar = Polynomial.X ^ 2 + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using
    (Polynomial.cyclotomic_prime_pow_eq_geom_sum
      (R := Scalar) (p := 2) (n := 1) Nat.prime_two)

theorem cyclotomic_four_eq :
    Polynomial.cyclotomic 4 ℝ = Polynomial.X ^ 2 + 1 :=
  cyclotomic_four ℝ

theorem aeval_cyclotomic_four (matrix : Mat2) :
    Polynomial.aeval matrix (Polynomial.cyclotomic 4 ℝ) = matrix ^ 2 + 1 := by
  rw [cyclotomic_four_eq]
  simp

theorem Eminus_cyclotomic_four :
    Polynomial.aeval Eminus (Polynomial.cyclotomic 4 ℝ) = 0 := by
  rw [aeval_cyclotomic_four, pow_two, Eminus_sq]
  simp

theorem polynomial_root_transport (hom : Mat2 →ₐ[ℝ] Mat2)
    (polynomial : Polynomial ℝ) (matrix : Mat2)
    (hroot : Polynomial.aeval matrix polynomial = 0) :
    Polynomial.aeval (hom matrix) polynomial = 0 := by
  rw [Polynomial.aeval_algHom_apply, hroot, map_zero]

theorem cyclotomic_four_conjugation (changeOfBasis : Mat2ˣ) (matrix : Mat2)
    (hroot : Polynomial.aeval matrix (Polynomial.cyclotomic 4 ℝ) = 0) :
    Polynomial.aeval
      ((changeOfBasis : Mat2) * matrix * ((changeOfBasis⁻¹ : Mat2ˣ) : Mat2))
      (Polynomial.cyclotomic 4 ℝ) = 0 := by
  have hsquare : matrix ^ 2 = -1 := by
    rw [aeval_cyclotomic_four] at hroot
    exact add_eq_zero_iff_eq_neg.mp hroot
  rw [aeval_cyclotomic_four]
  have hconjugate :
      ((changeOfBasis : Mat2) * matrix * ((changeOfBasis⁻¹ : Mat2ˣ) : Mat2)) ^ 2 =
        (changeOfBasis : Mat2) * (matrix ^ 2) * ((changeOfBasis⁻¹ : Mat2ˣ) : Mat2) := by
    simp only [pow_two, mul_assoc, Units.inv_mul_cancel_left]
  rw [hconjugate, hsquare]
  simp

theorem NPart_sub_one (parameter : ℝ) :
    NPart parameter - 1 =
      parameter • InfoGeometry.Geometry.MoebiusChiralGeneratorClassification.NPlus := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [NPart, InfoGeometry.Geometry.MoebiusChiralGeneratorClassification.NPlus]

theorem shear_unipotent (parameter : ℝ) : (NPart parameter - 1) ^ 2 = 0 := by
  rw [pow_two, NPart_sub_one]
  simp [smul_mul_assoc, mul_smul_comm,
    InfoGeometry.Geometry.MoebiusChiralGeneratorClassification.NPlus_sq]

theorem NPart_eq_one_iff (parameter : ℝ) : NPart parameter = 1 ↔ parameter = 0 := by
  constructor
  · intro hequal
    have hentry := congrArg (fun matrix : Mat2 => matrix 0 1) hequal
    simpa [NPart] using hentry
  · rintro rfl
    ext row column
    fin_cases row <;> fin_cases column <;> simp [NPart]

def shearRoot (parameter : ℝ) : Mat2 :=
  NPart parameter * Eminus * NPart (-parameter)

theorem NPart_mul_neg (parameter : ℝ) :
    NPart parameter * NPart (-parameter) = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [NPart, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearRoot_eq_matrix (parameter : ℝ) :
    shearRoot parameter = !![-parameter, parameter ^ 2 + 1; -1, parameter] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [shearRoot, NPart, Eminus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem shearRoot_sq (parameter : ℝ) : shearRoot parameter ^ 2 = -1 := by
  rw [pow_two, shearRoot_eq_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem shearRoot_cyclotomic_four (parameter : ℝ) :
    Polynomial.aeval (shearRoot parameter) (Polynomial.cyclotomic 4 ℝ) = 0 := by
  rw [aeval_cyclotomic_four, shearRoot_sq, neg_add_cancel]

theorem shearRoot_pow_four (parameter : ℝ) : shearRoot parameter ^ 4 = 1 := by
  calc
    shearRoot parameter ^ 4 = (shearRoot parameter ^ 2) ^ 2 := by
      rw [← pow_mul]
    _ = 1 := by rw [shearRoot_sq]; simp

theorem shearRoot_injective : Function.Injective shearRoot := by
  intro first second hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hequal
  simpa [shearRoot_eq_matrix] using hentry

theorem infinite_shearRoot_range : Set.Infinite (Set.range shearRoot) :=
  Set.infinite_range_of_injective shearRoot_injective

theorem shearRoot_commute_iff (first second : ℝ) :
    Commute (shearRoot first) (shearRoot second) ↔ first = second := by
  constructor
  · intro hcommute
    have hentry := congrArg (fun matrix : Mat2 => matrix 1 0) hcommute.eq
    simp [shearRoot_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two] at hentry
    linarith
  · rintro rfl
    exact Commute.refl _

theorem shearRoot_trace (parameter : ℝ) : Matrix.trace (shearRoot parameter) = 0 := by
  simp [shearRoot_eq_matrix, Matrix.trace, Fin.sum_univ_two]

theorem shearRoot_det (parameter : ℝ) : (shearRoot parameter).det = 1 := by
  rw [shearRoot_eq_matrix]
  simp [Matrix.det_fin_two]
  ring

theorem shearRoot_trace_discriminant (parameter : ℝ) :
    Matrix.trace (shearRoot parameter) ^ 2 - 4 * (shearRoot parameter).det = -4 := by
  rw [shearRoot_trace, shearRoot_det]
  norm_num

end InfoGeometry.Algebra.MatrixCyclotomics
