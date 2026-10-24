/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.PeirceHyperbolicComplement

/-! Completing active-corner matrix units to actual ambient units. The
complement is fixed, so full support is unnecessary. -/
namespace InfoGeometry.Canonical.PeirceMatrixUnitCompletion
open ReflexiveNilpotentFlows
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def completedMatrix (d B : A) (M : Matrix (Fin 2) (Fin 2) R) : A :=
  complement d B + pairMatrixLinear d B M

variable {d B : A} (hd : d*d=0) (hB : B*B=0)
  (hr : d*B*d=d) (hs : B*d*B=B)
include hd hB hr hs

theorem complement_mul_matrix (M : Matrix (Fin 2) (Fin 2) R) :
    complement d B * pairMatrixLinear d B M = 0 := by
  unfold complement
  rw [sub_mul, one_mul, ← pairMatrixLinear_one (R := R),
    ← pairMatrixLinear_mul hd hB hr hs, one_mul, sub_self]

theorem matrix_mul_complement (M : Matrix (Fin 2) (Fin 2) R) :
    pairMatrixLinear d B M * complement d B = 0 := by
  unfold complement
  rw [mul_sub, mul_one, ← pairMatrixLinear_one (R := R),
    ← pairMatrixLinear_mul hd hB hr hs, mul_one, sub_self]

theorem completedMatrix_mul (M N : Matrix (Fin 2) (Fin 2) R) :
    completedMatrix d B M * completedMatrix d B N = completedMatrix d B (M*N) := by
  have hh : complement d B * complement d B = complement d B := by
    unfold complement
    noncomm_ring [support_sq hd hB hr hs]
  unfold completedMatrix
  rw [add_mul, mul_add, mul_add, hh, complement_mul_matrix hd hB hr hs,
    matrix_mul_complement hd hB hr hs, ← pairMatrixLinear_mul hd hB hr hs]
  simp

omit hd hB hr hs in
theorem completedMatrix_one :
    completedMatrix d B (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  rw [completedMatrix, pairMatrixLinear_one]
  simp [complement]

/-- Any invertible active matrix gives an ambient unit fixing the complement. -/
def completedUnit (M : (Matrix (Fin 2) (Fin 2) R)ˣ) : Aˣ where
  val := completedMatrix d B (M : Matrix (Fin 2) (Fin 2) R)
  inv := completedMatrix d B (↑M⁻¹ : Matrix (Fin 2) (Fin 2) R)
  val_inv := by
    rw [completedMatrix_mul hd hB hr hs]
    change completedMatrix d B (M.val * M.inv) = 1
    rw [M.val_inv, completedMatrix_one]
  inv_val := by
    rw [completedMatrix_mul hd hB hr hs]
    change completedMatrix d B (M.inv * M.val) = 1
    rw [M.inv_val, completedMatrix_one]

/-- A normalized split-root boost is an actual ambient unit, even for proper support. -/
def hyperbolicUnit (u v : R) (h : u*u-v*v=1) : Aˣ :=
  completedUnit hd hB hr hs
    { val := !![u, v; v, u]
      inv := !![u, -v; -v, u]
      val_inv := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← sub_eq_add_neg, h, mul_comm]
        linear_combination h
      inv_val := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← sub_eq_add_neg, h, mul_comm]
        linear_combination h }

theorem hyperbolicUnit_val (u v : R) (h : u*u-v*v=1) :
    (hyperbolicUnit hd hB hr hs u v h : A) =
      complement d B + u • support d B + v • (d+B) := by
  simp [hyperbolicUnit, completedUnit, completedMatrix, pairMatrixLinear_apply,
    pairMatrixUnit, support, smul_add]
  abel

theorem completedMatrix_sandwich (M X N : Matrix (Fin 2) (Fin 2) R) :
    completedMatrix d B M * pairMatrixLinear d B X * completedMatrix d B N =
      pairMatrixLinear d B (M*X*N) := by
  unfold completedMatrix
  rw [add_mul, complement_mul_matrix hd hB hr hs, zero_add,
    ← pairMatrixLinear_mul hd hB hr hs, mul_add,
    matrix_mul_complement hd hB hr hs, zero_add,
    ← pairMatrixLinear_mul hd hB hr hs]

theorem hyperbolicUnit_conjugates_plus (u v : R) (h : u*u-v*v=1) :
    (hyperbolicUnit hd hB hr hs u v h : A) * (d*B) *
      (↑(hyperbolicUnit hd hB hr hs u v h)⁻¹ : A) =
      PeirceHyperbolicOrbit.hyperbolicPlus u v d B := by
  have hp : pairMatrixLinear d B (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) = d*B := by
    simp [pairMatrixLinear_apply, pairMatrixUnit]
  change completedMatrix d B !![u, v; v, u] * (d*B) *
    completedMatrix d B !![u, -v; -v, u] = _
  rw [← hp, completedMatrix_sandwich hd hB hr hs]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PeirceHyperbolicOrbit.hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end InfoGeometry.Canonical.PeirceMatrixUnitCompletion
