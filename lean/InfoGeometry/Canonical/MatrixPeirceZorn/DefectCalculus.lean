/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Bilinear associator calculus and noncommutative matrix Jordan algebra

All products in the first section are native additive bilinear maps.  No
associativity assumption is made.  The Teichmüller identity proved here is
an additive identity; no categorical coherence or cohomology structure is
asserted.  The second section supplies ordinary matrix composition and its
symmetrization as concrete bilinear maps on arbitrary complex matrices.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.DefectCalculus

universe u v

section Bilinear

variable {A : Type u} [AddCommGroup A]

/-- The associator of an additive bilinear multiplication. -/
def associator (μ : A →+ A →+ A) (x y z : A) : A :=
  μ (μ x y) z - μ x (μ y z)

/-- The commutator of an additive bilinear multiplication. -/
def commutator (μ : A →+ A →+ A) (x y : A) : A :=
  μ x y - μ y x

/-- The cyclic left-nested Jacobiator. -/
def jacobiator (μ : A →+ A →+ A) (x y z : A) : A :=
  commutator μ (commutator μ x y) z +
  commutator μ (commutator μ y z) x +
  commutator μ (commutator μ z x) y

/-- The five-term additive Teichmüller identity, valid without associativity. -/
theorem teichmueller (μ : A →+ A →+ A) (w x y z : A) :
    μ w (associator μ x y z) - associator μ (μ w x) y z +
      associator μ w (μ x y) z - associator μ w x (μ y z) +
      μ (associator μ w x y) z = 0 := by
  simp only [associator, map_sub, AddMonoidHom.sub_apply]
  abel

/-- Equality of the two additive reassociation paths. -/
theorem associator_reassociation (μ : A →+ A →+ A) (w x y z : A) :
    associator μ (μ w x) y z + associator μ w x (μ y z) =
      μ (associator μ w x y) z + associator μ w (μ x y) z +
      μ w (associator μ x y z) := by
  simp only [associator, map_sub, AddMonoidHom.sub_apply]
  abel

/-- The commutator Leibniz defect is the indicated three associators. -/
theorem commutator_leibniz_defect (μ : A →+ A →+ A) (x y z : A) :
    commutator μ (μ x y) z -
      (μ x (commutator μ y z) + μ (commutator μ x z) y) =
      associator μ x y z - associator μ x z y + associator μ z x y := by
  simp only [commutator, associator, map_sub, AddMonoidHom.sub_apply]
  abel

/-- The universal Akivis identity: Jacobiator equals alternating associator. -/
theorem jacobiator_eq_alternating_associator (μ : A →+ A →+ A) (x y z : A) :
    jacobiator μ x y z =
      associator μ x y z + associator μ y z x + associator μ z x y -
        associator μ y x z - associator μ z y x - associator μ x z y := by
  simp only [jacobiator, commutator, associator, map_sub, AddMonoidHom.sub_apply]
  abel

theorem commutator_skew (μ : A →+ A →+ A) (x y : A) :
    commutator μ x y = -commutator μ y x := by
  simp only [commutator]
  abel

theorem commutator_self (μ : A →+ A →+ A) (x : A) :
    commutator μ x x = 0 := sub_self _

/-- Associativity implies the Jacobi identity for the induced commutator. -/
theorem jacobiator_eq_zero_of_associative (μ : A →+ A →+ A)
    (hμ : ∀ x y z, μ (μ x y) z = μ x (μ y z)) (x y z : A) :
    jacobiator μ x y z = 0 := by
  rw [jacobiator_eq_alternating_associator]
  simp only [associator, hμ, sub_self, add_zero]

end Bilinear

section Matrices

variable {n : Type v} [Fintype n] [DecidableEq n]

abbrev Op (n : Type v) := Matrix n n ℂ

/-- Ordinary, generally noncommutative matrix composition as a bilinear map. -/
def matrixMul : Op n →+ Op n →+ Op n where
  toFun X :=
    { toFun := fun Y => X * Y
      map_zero' := mul_zero X
      map_add' := fun Y Z => mul_add X Y Z }
  map_zero' := by apply AddMonoidHom.ext; intro Y; exact zero_mul Y
  map_add' X Y := by apply AddMonoidHom.ext; intro Z; exact add_mul X Y Z

@[simp] theorem matrixMul_apply (X Y : Op n) : matrixMul X Y = X * Y := rfl

/-- The doubled Jordan product; it uses no division and retains matrix order. -/
def jordanMul : Op n →+ Op n →+ Op n where
  toFun X :=
    { toFun := fun Y => X * Y + Y * X
      map_zero' := by simp
      map_add' := by intro Y Z; noncomm_ring }
  map_zero' := by apply AddMonoidHom.ext; intro Y; simp
  map_add' X Y := by
    apply AddMonoidHom.ext
    intro Z
    change (X + Y) * Z + Z * (X + Y) = (X * Z + Z * X) + (Y * Z + Z * Y)
    noncomm_ring

@[simp] theorem jordanMul_apply (X Y : Op n) :
    jordanMul X Y = X * Y + Y * X := rfl

theorem jordanMul_comm (X Y : Op n) : jordanMul X Y = jordanMul Y X := by
  simp only [jordanMul_apply, add_comm]

theorem matrix_associator_eq_zero (X Y Z : Op n) :
    associator matrixMul X Y Z = 0 := by
  simp only [associator, matrixMul_apply, mul_assoc, sub_self]

/-- Nonassociativity of the Jordan product is exactly a double matrix commutator. -/
theorem jordan_associator_eq_double_commutator (X Y Z : Op n) :
    associator jordanMul X Y Z =
      commutator matrixMul Y (commutator matrixMul X Z) := by
  simp only [associator, commutator, jordanMul_apply, matrixMul_apply]
  noncomm_ring

/-- The Jordan identity, for the doubled product on arbitrary matrices. -/
theorem jordan_identity (X Y : Op n) :
    jordanMul (jordanMul (jordanMul X X) Y) X =
      jordanMul (jordanMul X X) (jordanMul Y X) := by
  simp only [jordanMul_apply]
  noncomm_ring

theorem jordan_flexible (X Y : Op n) :
    associator jordanMul X Y X = 0 := by
  rw [jordan_associator_eq_double_commutator, commutator_self]
  simp [commutator]

theorem matrix_jacobiator_eq_zero (X Y Z : Op n) :
    jacobiator matrixMul X Y Z = 0 :=
  jacobiator_eq_zero_of_associative matrixMul (fun _ _ _ => mul_assoc _ _ _) X Y Z

/-- Inner matrix commutators are genuine derivations of matrix composition. -/
theorem matrix_commutator_derivation (H X Y : Op n) :
    commutator matrixMul H (X * Y) =
      commutator matrixMul H X * Y + X * commutator matrixMul H Y := by
  simp only [commutator, matrixMul_apply]
  noncomm_ring

/-- Inner matrix commutators also preserve the Jordan multiplication. -/
theorem matrix_commutator_jordan_derivation (H X Y : Op n) :
    commutator matrixMul H (jordanMul X Y) =
      jordanMul (commutator matrixMul H X) Y +
        jordanMul X (commutator matrixMul H Y) := by
  simp only [commutator, matrixMul_apply, jordanMul_apply]
  noncomm_ring

/-- The Hermitian subspace is closed under the doubled Jordan product. -/
theorem jordanMul_isHermitian {X Y : Op n}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (jordanMul X Y).IsHermitian := by
  simp only [Matrix.IsHermitian, jordanMul_apply, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hX.eq, hY.eq, add_comm]

/-- A commutator of Hermitian matrices is skew-Hermitian. -/
theorem hermitian_commutator_conjTranspose {X Y : Op n}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (commutator matrixMul X Y).conjTranspose = -commutator matrixMul X Y := by
  simp only [commutator, matrixMul_apply, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hX.eq, hY.eq]
  abel

end Matrices

end InfoGeometry.Canonical.MatrixPeirceZorn.DefectCalculus
