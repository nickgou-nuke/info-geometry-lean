import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.BiQuaternionKahlerSymplectic

Finite symplectic owner lane for the biquaternion/Kähler corridor.

This file does not construct a smooth hyperkähler manifold, Hamiltonian vector
fields, Legendre transforms, or global Poisson geometry. It closes a finite
`R^4` theorem surface: the first quaternionic complex structure, its Kähler
readout, bilinearity, skewness, self-vanishing, and a concrete positivity
readback showing that every nonzero vector has a symplectic witness.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `symplecticI_formula`
- `symplecticI_skew`
- `symplecticI_add_left`, `symplecticI_add_right`
- `symplecticI_smul_left`, `symplecticI_smul_right`
- `symplecticI_self_zero`
- `symplecticI_apply_I4c_mulVec`
- `dot4_pos_of_exists_ne_zero`
- `exists_symplectic_witness_of_nonzero`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `exists_symplectic_witness_of_nonzero`

#### BUCKET 3: OPEN CLOSURE DEBT
Smooth/nonlinear symplectic geometry, nondegeneracy as an abstract bundle form,
Hamiltonian vector fields, Jacobi identity on function algebras, and analytic
Kähler potential machinery.
-/

namespace InfoGeometry.Canonical.BiQuaternionKahlerSymplectic

open Matrix

abbrev R4 : Type := InfoGeometry.Algebra.FiniteSpin.Vec4R
abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- Euclidean finite dot product on `R^4`. -/
def dot4 (x y : R4) : ℝ :=
  ∑ i, x i * y i

/-- First quaternionic complex structure on `R^4`. -/
def I4c : Mat4 :=
  !![(0 : ℝ), -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, 0]

/-- Finite Kähler readout from the first complex structure. -/
def symplecticI (x y : R4) : ℝ :=
  dot4 (I4c.mulVec x) y

theorem I4c_sq : I4c * I4c = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I4c, Matrix.mul_apply, Fin.sum_univ_four]

theorem symplecticI_formula (x y : R4) :
    symplecticI x y = -x 1 * y 0 + x 0 * y 1 - x 3 * y 2 + x 2 * y 3 := by
  dsimp [symplecticI, dot4]
  simp [I4c, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem symplecticI_skew (x y : R4) :
    symplecticI x y = -symplecticI y x := by
  rw [symplecticI_formula, symplecticI_formula]
  ring

theorem symplecticI_add_left (x z y : R4) :
    symplecticI (x + z) y = symplecticI x y + symplecticI z y := by
  rw [symplecticI_formula, symplecticI_formula, symplecticI_formula]
  simp
  ring_nf

theorem symplecticI_add_right (x y z : R4) :
    symplecticI x (y + z) = symplecticI x y + symplecticI x z := by
  rw [symplecticI_formula, symplecticI_formula, symplecticI_formula]
  simp
  ring_nf

theorem symplecticI_smul_left (a : ℝ) (x y : R4) :
    symplecticI (a • x) y = a * symplecticI x y := by
  rw [symplecticI_formula, symplecticI_formula]
  simp
  ring_nf

theorem symplecticI_smul_right (a : ℝ) (x y : R4) :
    symplecticI x (a • y) = a * symplecticI x y := by
  rw [symplecticI_formula, symplecticI_formula]
  simp
  ring_nf

theorem symplecticI_self_zero (x : R4) :
    symplecticI x x = 0 := by
  have h := symplecticI_skew x x
  linarith

theorem symplecticI_apply_I4c_mulVec (x : R4) :
    symplecticI x (I4c.mulVec x) = dot4 x x := by
  dsimp [symplecticI, dot4]
  simp [I4c, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem dot4_pos_of_exists_ne_zero (x : R4) (hx : ∃ i : Fin 4, x i ≠ 0) :
    0 < dot4 x x := by
  rcases hx with ⟨i, hi⟩
  fin_cases i
  · dsimp [dot4]
    simp [Fin.sum_univ_succ]
    have h0 : 0 < x 0 * x 0 := by
      exact mul_self_pos.2 hi
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3), h0]
  · dsimp [dot4]
    simp [Fin.sum_univ_succ]
    have h1 : 0 < x 1 * x 1 := by
      exact mul_self_pos.2 hi
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h1]
  · dsimp [dot4]
    simp [Fin.sum_univ_succ]
    have h2 : 0 < x 2 * x 2 := by
      exact mul_self_pos.2 hi
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 3), h2]
  · dsimp [dot4]
    simp [Fin.sum_univ_succ]
    have h3 : 0 < x 3 * x 3 := by
      exact mul_self_pos.2 hi
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), h3]

theorem exists_symplectic_witness_of_nonzero (x : R4) (hx : ∃ i : Fin 4, x i ≠ 0) :
    ∃ y : R4, 0 < symplecticI x y := by
  refine ⟨I4c.mulVec x, ?_⟩
  rw [symplecticI_apply_I4c_mulVec]
  exact dot4_pos_of_exists_ne_zero x hx

end InfoGeometry.Canonical.BiQuaternionKahlerSymplectic
