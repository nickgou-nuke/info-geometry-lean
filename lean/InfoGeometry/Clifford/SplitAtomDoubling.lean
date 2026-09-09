import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.BottPeriodicity

/-!
# Sign-twisted matrix doubling above the existing graded Clifford tower

`BottPeriodicity.splitBottStep` remains the owner of the graded tensor
factorization.  Here we prove the concrete block identities needed to
pass to an ordinary matrix model: old odd generators acquire opposite
diagonal signs.  The twisted map is linear, not multiplicative.  In contrast,
the repeated diagonal map is an actual ring homomorphism.

No octonion multiplication or exceptional Lie algebra is identified with
these associative matrices, and no unproved all-stage Clifford equivalence
is introduced.
-/

namespace InfoGeometry.Clifford.SplitAtomDoubling

section Blocks

variable {A : Type*} [Ring A]

abbrev Block2 (A : Type*) := Matrix (Fin 2) (Fin 2) A

def repeated (a : A) : Block2 A := !![a, 0; 0, a]

def twisted (a : A) : Block2 A := !![a, 0; 0, -a]

def positive : Block2 A := !![0, 1; 1, 0]

def negative : Block2 A := !![0, 1; -1, 0]

def repeatedHom : A →+* Block2 A where
  toFun := repeated
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [repeated]
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [repeated]
  map_add' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [repeated]
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [repeated, Matrix.mul_apply, Fin.sum_univ_two]

theorem twisted_injective : Function.Injective (twisted (A := A)) := by
  intro a b h
  exact congrArg (fun M : Block2 A => M 0 0) h

theorem twisted_mul (a b : A) : twisted a * twisted b = repeated (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, repeated, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem positive_square : (positive : Block2 A) * positive = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem negative_square : (negative : Block2 A) * negative = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negative, Matrix.mul_apply, Fin.sum_univ_two]

theorem head_anticommutator :
    (positive : Block2 A) * negative + negative * positive = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positive, negative, Matrix.mul_apply, Fin.sum_univ_two]

theorem twisted_positive_anticommutator (a : A) :
    twisted a * positive + positive * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, positive, Matrix.mul_apply, Fin.sum_univ_two]

theorem twisted_negative_anticommutator (a : A) :
    twisted a * negative + negative * twisted a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twisted, negative, Matrix.mul_apply, Fin.sum_univ_two]

/-- The old Clifford anticommutator is retained on the repeated diagonal. -/
theorem twisted_anticommutator (a b : A) :
    twisted a * twisted b + twisted b * twisted a = repeated (a * b + b * a) := by
  rw [twisted_mul, twisted_mul]
  exact (repeatedHom.map_add _ _).symm

end Blocks

/-- Size of a proposed matrix realization, not a new definition of Cl(n,n). -/
abbrev MatrixModel (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ

theorem matrixModel_finrank (n : ℕ) : Module.finrank ℝ (MatrixModel n) = 4 ^ n := by
  calc
    Module.finrank ℝ (MatrixModel n) = 2 ^ n * 2 ^ n := by
      simp [MatrixModel, Module.finrank_matrix]
    _ = (2 * 2) ^ n := (mul_pow 2 2 n).symm
    _ = 4 ^ n := by norm_num

theorem matrixModel_three_finrank : Module.finrank ℝ (MatrixModel 3) = 64 := by
  rw [matrixModel_finrank]; norm_num

theorem matrixModel_four_finrank : Module.finrank ℝ (MatrixModel 4) = 256 := by
  rw [matrixModel_finrank]; norm_num

end InfoGeometry.Clifford.SplitAtomDoubling
