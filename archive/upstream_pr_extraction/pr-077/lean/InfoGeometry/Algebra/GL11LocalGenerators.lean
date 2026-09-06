import InfoGeometry.Algebra.GL11GradedSwap

/-!
# The defining `gl(1|1)` matrix representation

On the ordered homogeneous basis `(e₀,e₁)`, with `e₀` even and `e₁` odd, this
file defines the four matrix units of `gl(1|1)`.  The diagonal generators are
even and the off-diagonal generators are odd.  Their products and
supercommutators are proved by direct finite matrix calculation.
-/

namespace InfoGeometry.Algebra.GL11LocalGenerators

open Matrix
open InfoGeometry.Algebra.GL11GradedSwap
open scoped Matrix

/-- The even matrix unit `E₀₀`. -/
def E00 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- The even matrix unit `E₁₁`. -/
def E11 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

/-- The odd matrix unit `E₀₁`. -/
def E01 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- The odd matrix unit `E₁₀`. -/
def E10 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 1, 0]

private theorem matrix_fin_two_ext
    {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ i j, A i j = B i j) : A = B :=
  Matrix.ext fun i j => h i j

/-- `E₀₀ + E₁₁` is the identity of the defining representation. -/
theorem E00_add_E11 :
    E00 + E11 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [E00, E11]

/-- The first odd generator is nilpotent. -/
theorem E01_sq :
    E01 * E01 = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [E01, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second odd generator is nilpotent. -/
theorem E10_sq :
    E10 * E10 = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [E10, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product `E₀₁E₁₀` is `E₀₀`. -/
theorem E01_mul_E10 :
    E01 * E10 = E00 := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [E00, E01, E10, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product `E₁₀E₀₁` is `E₁₁`. -/
theorem E10_mul_E01 :
    E10 * E01 = E11 := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [E01, E10, E11, Matrix.mul_apply, Fin.sum_univ_two]

/-- The odd supercommutator closes on the identity:
`{E₀₁,E₁₀} = E₀₀ + E₁₁ = 1`. -/
theorem odd_anticommutator :
    E01 * E10 + E10 * E01 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [E01_mul_E10, E10_mul_E01, E00_add_E11]

/-- `E₀₀` is even for the standard parity. -/
theorem E00_even :
    localParity * E00 = E00 * localParity := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [localParity, E00,
      InfoGeometry.Algebra.SupermatrixKoszul.parityBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₁₁` is even for the standard parity. -/
theorem E11_even :
    localParity * E11 = E11 * localParity := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [localParity, E11,
      InfoGeometry.Algebra.SupermatrixKoszul.parityBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₀₁` anticommutes with parity. -/
theorem E01_odd :
    localParity * E01 = -(E01 * localParity) := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [localParity, E01,
      InfoGeometry.Algebra.SupermatrixKoszul.parityBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₁₀` anticommutes with parity. -/
theorem E10_odd :
    localParity * E10 = -(E10 * localParity) := by
  apply matrix_fin_two_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [localParity, E10,
      InfoGeometry.Algebra.SupermatrixKoszul.parityBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Algebra.GL11LocalGenerators
