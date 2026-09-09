import InfoGeometry.Algebra.GL11LocalGenerators
import InfoGeometry.Algebra.LogarithmicJordanPair

/-!
# A concrete zero-loop Temperley--Lieb representation

At `q = I`, the usual two-site Temperley--Lieb matrix has loop parameter
`q + q⁻¹ = 0`.  This file proves the defining relations directly on two and
three copies of `ℂ²`.  It does not identify this finite representation with a
particular Hamiltonian or continuum theory.
-/

namespace InfoGeometry.Algebra.TemperleyLiebZeroLoop

open Matrix
open scoped Matrix ComplexConjugate

/-- The standard two-site Temperley--Lieb generator at `q = I`, in basis
`(00,01,10,11)`. -/
def generator : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, Complex.I, 1, 0;
     0, 1, -Complex.I, 0;
     0, 0, 0, 0]

/-- The loop parameter vanishes at `q = I`. -/
theorem loopParameter_eq_zero :
    Complex.I + Complex.I⁻¹ = 0 := by
  rw [Complex.inv_I]
  simp

/-- The two-site generator is nilpotent, the `δ = 0` specialization of
`e² = δe`. -/
theorem generator_sq_zero :
    generator * generator = (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

/-- A nonzero vector in the image and kernel of the zero-loop generator. -/
def jordanEigenvector : Fin 4 → ℂ :=
  ![0, 1, -Complex.I, 0]

/-- A generalized eigenvector mapped to `jordanEigenvector`. -/
def jordanGeneralized : Fin 4 → ℂ :=
  ![0, 0, 1, 0]

/-- The matrix generator as a native linear endomorphism. -/
def generatorEnd : Module.End ℂ (Fin 4 → ℂ) :=
  Matrix.mulVecLin generator

/-- The proposed eigenvector is genuinely nonzero. -/
theorem jordanEigenvector_ne_zero :
    jordanEigenvector ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  simp [jordanEigenvector] at h1

/-- The generator kills the image vector. -/
theorem generator_mulVec_jordanEigenvector :
    generator.mulVec jordanEigenvector = 0 := by
  funext i
  fin_cases i <;>
    simp [generator, jordanEigenvector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Complex.I_mul_I]

/-- The generator maps the generalized vector to the nonzero eigenvector. -/
theorem generator_mulVec_jordanGeneralized :
    generator.mulVec jordanGeneralized = jordanEigenvector := by
  funext i
  fin_cases i <;>
    simp [generator, jordanEigenvector, jordanGeneralized, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]

/-- The displayed vectors form a genuine rank-two Jordan pair at eigenvalue
zero. -/
theorem isJordanPair_generatorEnd :
    LogarithmicJordanPair.IsJordanPair generatorEnd 0
      jordanEigenvector jordanGeneralized := by
  refine ⟨jordanEigenvector_ne_zero, ?_, ?_⟩
  · simpa [generatorEnd] using generator_mulVec_jordanEigenvector
  · simpa [generatorEnd] using generator_mulVec_jordanGeneralized

/-- The zero-loop Temperley--Lieb generator has a finite logarithmic Jordan
cell.  This is a finite non-semisimplicity theorem, not a continuum-limit
claim. -/
theorem generatorEnd_hasLogarithmicJordanCell :
    LogarithmicJordanPair.HasLogarithmicJordanCell generatorEnd :=
  LogarithmicJordanPair.hasLogarithmicJordanCell_of_isJordanPair
    isJordanPair_generatorEnd

/-- Exact rank-two nilpotence on the explicit generalized vector. -/
theorem generatorEnd_rank_two_nilpotence :
    (LogarithmicJordanPair.shifted generatorEnd 0).comp
          (LogarithmicJordanPair.shifted generatorEnd 0) jordanGeneralized = 0 ∧
      LogarithmicJordanPair.shifted generatorEnd 0 jordanGeneralized ≠ 0 :=
  LogarithmicJordanPair.rank_two_shifted_nilpotence
    isJordanPair_generatorEnd

/-- A three-site basis index `(a,b,c)`. -/
abbrev Triple := Fin 2 × Fin 2 × Fin 2

private def pairEntry (a b c d : Fin 2) : ℂ :=
  if a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1 then Complex.I
  else if a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0 then 1
  else if a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1 then 1
  else if a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0 then -Complex.I
  else 0

/-- The generator acting on sites `1,2` of three sites. -/
def leftGenerator : Matrix Triple Triple ℂ :=
  fun x y =>
    pairEntry x.1 x.2.1 y.1 y.2.1 *
      if x.2.2 = y.2.2 then 1 else 0

/-- The generator acting on sites `2,3` of three sites. -/
def rightGenerator : Matrix Triple Triple ℂ :=
  fun x y =>
    (if x.1 = y.1 then 1 else 0) *
      pairEntry x.2.1 x.2.2 y.2.1 y.2.2

private theorem triple_matrix_ext
    {A B : Matrix Triple Triple ℂ}
    (h : ∀ i j, A i j = B i j) : A = B :=
  Matrix.ext fun i j => h i j

/-- The left three-site generator has loop parameter zero. -/
theorem leftGenerator_sq_zero :
    leftGenerator * leftGenerator = (0 : Matrix Triple Triple ℂ) := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [leftGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- The right three-site generator has loop parameter zero. -/
theorem rightGenerator_sq_zero :
    rightGenerator * rightGenerator = (0 : Matrix Triple Triple ℂ) := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [rightGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- First adjacent Temperley--Lieb relation. -/
theorem left_right_left :
    leftGenerator * rightGenerator * leftGenerator = leftGenerator := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [leftGenerator, rightGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

/-- Second adjacent Temperley--Lieb relation. -/
theorem right_left_right :
    rightGenerator * leftGenerator * rightGenerator = rightGenerator := by
  apply triple_matrix_ext
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [leftGenerator, rightGenerator, pairEntry, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.I_mul_I]

end InfoGeometry.Algebra.TemperleyLiebZeroLoop
