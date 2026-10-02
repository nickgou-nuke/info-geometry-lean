import InfoGeometry.Algebra.CuntzMatrixUnits
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# A real split Clifford representation from the owned Cuntz matrix units

The coefficient carrier is the existing *algebraic* Cuntz quotient, viewed
as a real algebra. No C*-completion, faithful representation, modular
standard form, dynamics, or spectral identification is asserted.

The construction uses `E_ij = S_i Sdag_j`, not the non-surjective isometries
as square-one Clifford generators. The final map uses the native universal
property `CliffordAlgebra.lift` for `x0^2 + x1^2 - x2^2 - x3^2`.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzClifford22

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzMatrixUnits
open scoped Matrix

/-- Restriction of scalars, without changing the owned quotient or its product. -/
abbrev Coeff := RestrictScalars ℝ ℂ (CuntzAlg 2)

/-- Transport the existing formal involution through the scalar-restriction alias. -/
instance coeffStar : Star Coeff := inferInstanceAs (Star (CuntzAlg 2))

instance coeffStarRing : StarRing Coeff := inferInstanceAs (StarRing (CuntzAlg 2))

/-- The extra two-sheet block factor. -/
abbrev Block := Matrix (Fin 2) (Fin 2) Coeff

/-- Reuse of the existing matrix-unit owner. -/
abbrev e (i j : Fin 2) : Coeff := E 2 i j

@[simp] theorem e_mul (i j k l : Fin 2) :
    e i j * e k l = if j = k then e i l else 0 :=
  matrix_unit_mul 2 i j k l

@[simp] theorem e_star (i j : Fin 2) : star (e i j) = e j i :=
  matrix_unit_star 2 i j

/-- Completeness of the two range projections. -/
theorem diagonal_sum : e 0 0 + e 1 1 = 1 := by
  simpa [Fin.sum_univ_two] using matrix_unit_sum_diag_eq_one 2

/-- Symmetric off-diagonal direction. -/
def u : Coeff := e 0 1 + e 1 0

/-- Diagonal split direction. -/
def v : Coeff := e 0 0 - e 1 1

/-- Real skew direction. -/
def w : Coeff := e 0 1 - e 1 0

@[simp] theorem u_sq : u * u = 1 := by
  simpa [u, mul_add, add_mul, add_comm] using diagonal_sum

@[simp] theorem v_sq : v * v = 1 := by
  simpa [v, mul_sub, sub_mul] using diagonal_sum

@[simp] theorem w_sq : w * w = -1 := by
  calc
    w * w = -(e 0 0 + e 1 1) := by
      simp [w, mul_sub, sub_mul]
      abel
    _ = -1 := by rw [diagonal_sum]

@[simp] theorem u_v : u * v = -w := by
  simp [u, v, w, add_mul, mul_sub]

@[simp] theorem v_u : v * u = w := by
  simp [u, v, w, sub_mul, mul_add]
  abel

@[simp] theorem u_w : u * w = -v := by
  simp [u, v, w, add_mul, mul_sub]

@[simp] theorem w_u : w * u = v := by
  simp [u, v, w, sub_mul, mul_add]
  abel

@[simp] theorem v_w : v * w = u := by
  simp [u, v, w, sub_mul, mul_sub]

@[simp] theorem w_v : w * v = -u := by
  simp [u, v, w, sub_mul, mul_sub]
  abel

@[simp] theorem star_u : star u = u := by
  simp only [u, star_add, e_star]
  abel
@[simp] theorem star_v : star v = v := by
  simp only [v, star_sub, e_star]
@[simp] theorem star_w : star w = -w := by
  simp only [w, star_sub, e_star]
  abel

/-- The four corrected block generators, ordered with signs `+,+,-,-`. -/
def gamma : Fin 4 → Block :=
  ![!![0, 1; 1, 0], !![0, w; -w, 0],
    !![0, u; -u, 0], !![0, v; -v, 0]]

/-- Coordinate linear forms on the real generator space. -/
def coordinate (i : Fin 4) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i

/-- Native quadratic form of signature `(2,2)`. -/
def quadratic : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.linMulLin (coordinate 0) (coordinate 0) +
    QuadraticMap.linMulLin (coordinate 1) (coordinate 1) -
    QuadraticMap.linMulLin (coordinate 2) (coordinate 2) -
    QuadraticMap.linMulLin (coordinate 3) (coordinate 3)

@[simp] theorem quadratic_apply (x : Fin 4 → ℝ) :
    quadratic x = x 0 * x 0 + x 1 * x 1 - x 2 * x 2 - x 3 * x 3 := by
  simp [quadratic, coordinate]

/-- The internal split-quaternionic part of a generator combination. -/
def spin (x : Fin 4 → ℝ) : Coeff := x 1 • w + x 2 • u + x 3 • v

theorem spin_square (x : Fin 4 → ℝ) :
    spin x * spin x = (-x 1 * x 1 + x 2 * x 2 + x 3 * x 3) • (1 : Coeff) := by
  simp only [spin, add_mul, mul_add, smul_mul_smul]
  rw [w_sq, u_sq, v_sq, w_u, u_w, w_v, v_w, u_v, v_u]
  module

/-- Real-linear map of generators into the two-sheet operator blocks. -/
def gammaVector : (Fin 4 → ℝ) →ₗ[ℝ] Block where
  toFun x := !![0, x 0 • (1 : Coeff) + spin x;
    x 0 • (1 : Coeff) - spin x, 0]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spin, add_smul] <;> abel
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spin, smul_add, smul_sub, smul_smul]

/-- The quadratic relation required by the universal Clifford lift. -/
theorem gammaVector_square (x : Fin 4 → ℝ) :
    gammaVector x * gammaVector x = algebraMap ℝ Block (quadratic x) := by
  have hL : (x 0 • (1 : Coeff) + spin x) * (x 0 • (1 : Coeff) - spin x) =
      quadratic x • (1 : Coeff) := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      spin_square, quadratic_apply]
    module
  have hR : (x 0 • (1 : Coeff) - spin x) * (x 0 • (1 : Coeff) + spin x) =
      quadratic x • (1 : Coeff) := by
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      spin_square, quadratic_apply]
    module
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [gammaVector, Matrix.mul_apply, Fin.sum_univ_two] using hL
  · simp [gammaVector, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [gammaVector, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [gammaVector, Matrix.mul_apply, Fin.sum_univ_two] using hR

/-- The representation is an actual native real algebra homomorphism. -/
def representation : CliffordAlgebra quadratic →ₐ[ℝ] Block :=
  CliffordAlgebra.lift quadratic ⟨gammaVector, gammaVector_square⟩

@[simp] theorem representation_iota (x : Fin 4 → ℝ) :
    representation (CliffordAlgebra.ι quadratic x) = gammaVector x := by
  simp [representation]

/-- Each stated block is the image of its corresponding native generator. -/
theorem gammaVector_basis (i : Fin 4) :
    gammaVector (Pi.single i (1 : ℝ)) = gamma i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [gammaVector, gamma, spin]

/-- Polarization derives every anticommutator from the full quadratic law. -/
theorem gammaVector_polarization (x y : Fin 4 → ℝ) :
    gammaVector x * gammaVector y + gammaVector y * gammaVector x =
      algebraMap ℝ Block (quadratic (x + y) - quadratic x - quadratic y) := by
  simp only [map_sub, ← gammaVector_square, map_add]
  noncomm_ring

/-- All sixteen Clifford relations follow without a matrix-entry case explosion. -/
theorem gamma_anticommutator (i j : Fin 4) :
    gamma i * gamma j + gamma j * gamma i =
      (if i = j then (if i.val < 2 then (2 : ℝ) else -2) else 0) • (1 : Block) := by
  rw [← gammaVector_basis i, ← gammaVector_basis j, gammaVector_polarization,
    Algebra.algebraMap_eq_smul_one]
  congr 1
  fin_cases i <;> fin_cases j <;> norm_num [quadratic_apply, Pi.single_apply, Fin.ext_iff]

/-- Generator-level readback from the universal representation. -/
theorem representation_basis (i : Fin 4) :
    representation (CliffordAlgebra.ι quadratic (Pi.single i (1 : ℝ))) = gamma i := by
  rw [representation_iota, gammaVector_basis]

end InfoGeometry.Algebra.CuntzClifford22
