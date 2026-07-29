import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Complex `Cl(4)` matrix periodicity corridor

This module records the complex-algebra lane for the `Cl(4, ℂ)` matrix model.

The verified matrix target is `Matrix (Fin 4) (Fin 4) ℂ`.  Quaternionic language
belongs to the real/bilingual readback lane; the bare real algebra `M₂(ℍ)` is not
silently interchangeable with the complex algebra `M₄(ℂ)`.
-/

open scoped Matrix

set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Clifford.Cl4ComplexMatrixPeriodicity

/-- Complex Clifford matrix shape: one simple block, or two simple blocks. -/
inductive ComplexCliffordShape where
  | simple (matrixSize : ℕ)
  | doubled (matrixSize : ℕ)
deriving DecidableEq, Repr

namespace ComplexCliffordShape

/-- Tensoring with `M₂(ℂ)` doubles each matrix block. -/
def tensorM2 : ComplexCliffordShape → ComplexCliffordShape
  | simple n => simple (n * 2)
  | doubled n => doubled (n * 2)

end ComplexCliffordShape

/--
The period-two complex Clifford matrix shape.

This is a shape-level formalization of
`Cl(n+2, ℂ) ≃ Cl(n, ℂ) ⊗ M₂(ℂ)`.
-/
def complexCliffordShape : ℕ → ComplexCliffordShape
  | 0 => .simple 1
  | 1 => .doubled 1
  | n + 2 => (complexCliffordShape n).tensorM2

@[simp] theorem complexCliffordShape_period_two (n : ℕ) :
    complexCliffordShape (n + 2) = (complexCliffordShape n).tensorM2 := by
  rfl

theorem complexCliffordShape_even (k : ℕ) :
    complexCliffordShape (2 * k) = .simple (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hnat : 2 * Nat.succ k = 2 * k + 2 := by omega
      rw [hnat]
      change (complexCliffordShape (2 * k)).tensorM2 = .simple (2 ^ Nat.succ k)
      rw [ih]
      simp [ComplexCliffordShape.tensorM2, pow_succ]

theorem complexCliffordShape_odd (k : ℕ) :
    complexCliffordShape (2 * k + 1) = .doubled (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hnat : 2 * Nat.succ k + 1 = (2 * k + 1) + 2 := by omega
      rw [hnat]
      change (complexCliffordShape (2 * k + 1)).tensorM2 = .doubled (2 ^ Nat.succ k)
      rw [ih]
      simp [ComplexCliffordShape.tensorM2, pow_succ]

@[simp] theorem complexCliffordShape_four :
    complexCliffordShape 4 = .simple 4 := by
  norm_num [complexCliffordShape, ComplexCliffordShape.tensorM2]

@[simp] theorem complexCliffordShape_nine :
    complexCliffordShape 9 = .doubled 16 := by
  norm_num [complexCliffordShape, ComplexCliffordShape.tensorM2]

abbrev Vec4 : Type := ℂ × ℂ × ℂ × ℂ
abbrev Mat4C : Type := Matrix (Fin 4) (Fin 4) ℂ

/-- Negative Euclidean quadratic form for generators squaring to `-1`. -/
noncomputable def q4neg : QuadraticForm ℂ Vec4 :=
  - (QuadraticMap.sq.prod (QuadraticMap.sq.prod (QuadraticMap.sq.prod QuadraticMap.sq)))

@[simp] theorem q4neg_apply (v : Vec4) :
    q4neg v = -(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2) := by
  simp [q4neg, QuadraticMap.prod_apply]
  ring

/--
`E₁ = (i σ₁) ⊗ σ₃`.

The `σ₃` tail is the graded tensor sign; without it the old and new generators
commute rather than anticommute.
-/
def E1 : Mat4C :=
  !![(0 : ℂ), 0, Complex.I, 0;
     0, 0, 0, -Complex.I;
     Complex.I, 0, 0, 0;
     0, -Complex.I, 0, 0]

/-- `E₂ = (i σ₂) ⊗ σ₃`. -/
def E2 : Mat4C :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, -1;
     -1, 0, 0, 0;
     0, 1, 0, 0]

/-- `E₃ = I₂ ⊗ (i σ₁)`. -/
def E3 : Mat4C :=
  !![(0 : ℂ), Complex.I, 0, 0;
     Complex.I, 0, 0, 0;
     0, 0, 0, Complex.I;
     0, 0, Complex.I, 0]

/-- `E₄ = I₂ ⊗ (i σ₂)`. -/
def E4 : Mat4C :=
  !![(0 : ℂ), 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

theorem E1_sq : E1 * E1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem E2_sq : E2 * E2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem E3_sq : E3 * E3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem E4_sq : E4 * E4 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem E1_E2_anticomm : E1 * E2 + E2 * E1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, E2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem E1_E3_anticomm : E1 * E3 + E3 * E1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, E3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem E1_E4_anticomm : E1 * E4 + E4 * E1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, E4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem E2_E3_anticomm : E2 * E3 + E3 * E2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E2, E3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem E2_E4_anticomm : E2 * E4 + E4 * E2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E2, E4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem E3_E4_anticomm : E3 * E4 + E4 * E3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E3, E4, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Linear Clifford generator map into `M₄(ℂ)`. -/
noncomputable def gen4 : Vec4 →ₗ[ℂ] Mat4C where
  toFun v := v.1 • E1 + v.2.1 • E2 + v.2.2.1 • E3 + v.2.2.2 • E4
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E1, E2, E3, E4, Matrix.add_apply, Matrix.smul_apply] <;> ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E1, E2, E3, E4, Matrix.add_apply, Matrix.smul_apply, mul_add] <;> ring

theorem gen4_basis_sq (a b c d : ℂ) :
    ((a • E1 + b • E2 + c • E3 + d • E4) *
        (a • E1 + b • E2 + c • E3 + d • E4)) =
      (-(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) • (1 : Mat4C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, E2, E3, E4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply,
      Matrix.add_apply] <;> ring_nf <;> simp <;> ring

theorem gen4_sq (v : Vec4) : gen4 v * gen4 v = algebraMap ℂ Mat4C (q4neg v) := by
  rcases v with ⟨a, b, c, d⟩
  simpa [gen4, q4neg_apply, Algebra.algebraMap_eq_smul_one] using
    gen4_basis_sq a b c d

/-- The induced complex-algebra representation of `Cl(4, ℂ)` in `M₄(ℂ)`. -/
noncomputable def cl4ToMat4 : CliffordAlgebra q4neg →ₐ[ℂ] Mat4C :=
  CliffordAlgebra.lift q4neg ⟨gen4, gen4_sq⟩

@[simp] theorem cl4ToMat4_ι (v : Vec4) :
    cl4ToMat4 (CliffordAlgebra.ι q4neg v) = gen4 v := by
  rw [cl4ToMat4, CliffordAlgebra.lift_ι_apply]

theorem mat4C_complex_finrank : Module.finrank ℂ Mat4C = 16 := by
  simp [Mat4C, Module.finrank_matrix, Fintype.card_fin]

/--
Dimension guard for the bilingual/quaternionic readback:
bare `M₂(ℍ)` has real dimension `2 * 2 * 4 = 16`, while `M₄(ℂ)` has real
dimension `4 * 4 * 2 = 32`.
-/
theorem bare_M2H_dimension_ne_M4C_real_dimension :
    (2 * 2 * 4 : ℕ) ≠ 4 * 4 * 2 := by
  norm_num

end InfoGeometry.Clifford.Cl4ComplexMatrixPeriodicity
