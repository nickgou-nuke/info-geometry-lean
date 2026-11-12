/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Group

/-!
# Weighted permutation matrices and ordered holonomy

For a permutation `σ`, the weighted shift has coefficient `U i` in row `i`,
column `σ i`. Its ordered holonomy with a diagonal family `V` is
`V i * U i * (V (σ i))⁻¹ * (U i)⁻¹`.

The family identities hold in an arbitrary group. Their matrix realization
uses units of an arbitrary ring and a finite decidable index type. Both the
diagonal family and the weighted shift are constructed as actual units of the matrix ring;
no determinant, commutative coefficient, or invertibility hypothesis is added.

The construction uses `Matrix.diagonalRingHom`, `MulEquiv.piUnits`,
`Equiv.Perm.permMatrix`, and the native `PEquiv` multiplication formulas.
The resulting identities concern finite matrices and vertexwise conjugation.
-/

namespace InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy

section GroupFamilies

variable {I G : Type*} [Group G]

/-- Ordered holonomy for the row-`i`, column-`σ i` convention. -/
def holonomy (σ : Equiv.Perm I) (U V : I → G) : I → G :=
  fun i => V i * U i * (V (σ i))⁻¹ * (U i)⁻¹

/-- A gauge change at the source and target of each permutation edge. -/
def linkGauge (σ : Equiv.Perm I) (g U : I → G) : I → G :=
  fun i => g i * U i * (g (σ i))⁻¹

/-- Conjugation of a family based at the vertices. -/
def vertexGauge (g V : I → G) : I → G :=
  fun i => g i * V i * (g i)⁻¹

/-- The holonomy is the coefficient required to exchange the two ordered factors. -/
theorem holonomy_ordered_braid (σ : Equiv.Perm I) (U V : I → G) (i : I) :
    V i * U i = holonomy σ U V i * U i * V (σ i) := by
  dsimp [holonomy]
  group

/-- The holonomy transforms by conjugation at its base vertex. -/
theorem holonomy_gauge_covariant (σ : Equiv.Perm I) (g U V : I → G) :
    holonomy σ (linkGauge σ g U) (vertexGauge g V) =
      vertexGauge g (holonomy σ U V) := by
  funext i
  dsimp [holonomy, linkGauge, vertexGauge]
  group

end GroupFamilies

section MatrixUnits

variable {I A : Type*} [Fintype I] [DecidableEq I] [Ring A]

/-- The native diagonal ring homomorphism, lifted to a group homomorphism on units. -/
def diagonalUnit : (I → Aˣ) →* (Matrix I I A)ˣ :=
  (Units.map (Matrix.diagonalRingHom I A).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : I => A)).symm.toMonoidHom

@[simp]
theorem coe_diagonalUnit (V : I → Aˣ) :
    (diagonalUnit V : Matrix I I A) = Matrix.diagonal (fun i => (V i : A)) :=
  rfl

@[simp]
theorem coe_diagonalUnit_inv (V : I → Aˣ) :
    (↑((diagonalUnit V)⁻¹) : Matrix I I A) =
      Matrix.diagonal (fun i => (↑((V i)⁻¹) : A)) :=
  rfl

/-- The permutation matrix as a unit, with the inverse permutation as its inverse. -/
def permutationUnit (σ : Equiv.Perm I) : (Matrix I I A)ˣ where
  val := σ.permMatrix A
  inv := (σ⁻¹).permMatrix A
  val_inv := by
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  inv_val := by
    rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

@[simp]
theorem coe_permutationUnit (σ : Equiv.Perm I) :
    (permutationUnit (A := A) σ : Matrix I I A) = σ.permMatrix A :=
  rfl

@[simp]
theorem coe_permutationUnit_inv (σ : Equiv.Perm I) :
    (↑((permutationUnit (A := A) σ)⁻¹) : Matrix I I A) = (σ⁻¹).permMatrix A :=
  rfl

/-- A diagonal family followed by the native permutation matrix. -/
def weightedShift (σ : Equiv.Perm I) (U : I → Aˣ) : (Matrix I I A)ˣ :=
  diagonalUnit U * permutationUnit σ

@[simp]
theorem coe_weightedShift (σ : Equiv.Perm I) (U : I → Aˣ) :
    (weightedShift σ U : Matrix I I A) =
      Matrix.diagonal (fun i => (U i : A)) * σ.permMatrix A :=
  rfl

@[simp]
theorem coe_weightedShift_inv (σ : Equiv.Perm I) (U : I → Aˣ) :
    (↑((weightedShift σ U)⁻¹) : Matrix I I A) =
      (σ⁻¹).permMatrix A * Matrix.diagonal (fun i => (↑((U i)⁻¹) : A)) :=
  rfl

/-- The entry formula fixes the permutation convention explicitly. -/
@[simp]
theorem weightedShift_apply (σ : Equiv.Perm I) (U : I → Aˣ) (i j : I) :
    (weightedShift σ U : Matrix I I A) i j =
      if j = σ i then (U i : A) else 0 := by
  simp [coe_weightedShift, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    mul_ite, eq_comm]

/-- Left multiplication uses the row action of the native permutation matrix. -/
theorem weightedShift_mul_apply (σ : Equiv.Perm I) (U : I → Aˣ)
    (M : Matrix I I A) (i j : I) :
    ((weightedShift σ U : Matrix I I A) * M) i j = (U i : A) * M (σ i) j := by
  simp only [coe_weightedShift, Matrix.mul_assoc, Matrix.diagonal_mul,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    Matrix.submatrix_apply, id_eq]

/-- Right multiplication uses the inverse permutation on the column index. -/
theorem mul_weightedShift_apply (σ : Equiv.Perm I) (U : I → Aˣ)
    (M : Matrix I I A) (i j : I) :
    (M * (weightedShift σ U : Matrix I I A)) i j =
      M i (σ.symm j) * (U (σ.symm j) : A) := by
  rw [coe_weightedShift, ← Matrix.mul_assoc]
  simp only [Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, id_eq, Matrix.mul_diagonal]

/-- The inverse is a weighted shift along the inverse permutation. -/
theorem weightedShift_inv (σ : Equiv.Perm I) (U : I → Aˣ) :
    (weightedShift σ U)⁻¹ =
      weightedShift σ⁻¹ (fun i => (U (σ⁻¹ i))⁻¹) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [coe_weightedShift_inv, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, id_eq,
    Matrix.diagonal_apply, weightedShift_apply, eq_comm]

/-- The ordered relation is an equality of actual units of the matrix ring. -/
theorem ordered_braid (σ : Equiv.Perm I) (U V : I → Aˣ) :
    diagonalUnit V * weightedShift σ U =
      diagonalUnit (holonomy σ U V) * weightedShift σ U * diagonalUnit V := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [Units.val_mul, coe_diagonalUnit, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : j = σ i
  · subst j
    simpa [weightedShift_apply, Units.val_mul] using
      congrArg (fun a : Aˣ => (a : A)) (holonomy_ordered_braid σ U V i)
  · simp [weightedShift_apply, hij]

/-- The same ordered relation in the underlying noncommutative matrix ring. -/
theorem matrix_ordered_braid (σ : Equiv.Perm I) (U V : I → Aˣ) :
    Matrix.diagonal (fun i => (V i : A)) * (weightedShift σ U : Matrix I I A) =
      Matrix.diagonal (fun i => (↑(holonomy σ U V i) : A)) *
        (weightedShift σ U : Matrix I I A) * Matrix.diagonal (fun i => (V i : A)) := by
  simpa only [Units.val_mul, coe_diagonalUnit] using
    congrArg (fun W : (Matrix I I A)ˣ => (W : Matrix I I A)) (ordered_braid σ U V)

/-- The group commutator of the diagonal and weighted shift equals the diagonal holonomy. -/
theorem global_commutator (σ : Equiv.Perm I) (U V : I → Aˣ) :
    diagonalUnit V * weightedShift σ U * (diagonalUnit V)⁻¹ * (weightedShift σ U)⁻¹ =
      diagonalUnit (holonomy σ U V) := by
  rw [ordered_braid σ U V]
  group

/-- An explicit matrix formula for the commutator, using the constructed unit inverse. -/
theorem matrix_global_commutator (σ : Equiv.Perm I) (U V : I → Aˣ) :
    Matrix.diagonal (fun i => (V i : A)) * (weightedShift σ U : Matrix I I A) *
        Matrix.diagonal (fun i => (↑((V i)⁻¹) : A)) *
        (↑((weightedShift σ U)⁻¹) : Matrix I I A) =
      Matrix.diagonal (fun i => (↑(holonomy σ U V i) : A)) := by
  simpa only [Units.val_mul, coe_diagonalUnit, coe_diagonalUnit_inv] using
    congrArg (fun W : (Matrix I I A)ˣ => (W : Matrix I I A)) (global_commutator σ U V)

/-- The diagonal homomorphism carries vertexwise conjugation to matrix conjugation. -/
theorem diagonalUnit_gauge_covariant (g V : I → Aˣ) :
    diagonalUnit (vertexGauge g V) =
      diagonalUnit g * diagonalUnit V * (diagonalUnit g)⁻¹ := by
  change diagonalUnit (g * V * g⁻¹) = _
  simp only [map_mul, map_inv]

/-- The endpoint gauge change of edge weights is diagonal conjugation of the shift. -/
theorem weightedShift_gauge_covariant (σ : Equiv.Perm I) (g U : I → Aˣ) :
    weightedShift σ (linkGauge σ g U) =
      diagonalUnit g * weightedShift σ U * (diagonalUnit g)⁻¹ := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [Units.val_mul, coe_diagonalUnit, coe_diagonalUnit_inv,
    Matrix.mul_diagonal, Matrix.diagonal_mul, weightedShift_apply]
  by_cases hij : j = σ i
  · subst j
    simp [linkGauge]
  · simp [hij]

/-- The holonomy matrix transforms by the same diagonal gauge conjugation. -/
theorem holonomyMatrix_gauge_covariant (σ : Equiv.Perm I) (g U V : I → Aˣ) :
    diagonalUnit (holonomy σ (linkGauge σ g U) (vertexGauge g V)) =
      diagonalUnit g * diagonalUnit (holonomy σ U V) * (diagonalUnit g)⁻¹ := by
  rw [holonomy_gauge_covariant, diagonalUnit_gauge_covariant]

end MatrixUnits

end InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy
