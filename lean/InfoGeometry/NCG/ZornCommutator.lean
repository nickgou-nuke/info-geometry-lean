/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

/-!
# Non-Commutative Zorn Commutator on `OpZornMatrix A`

Defines the operator-valued Zorn commutator `[X, Y] = X * Y - Y * X` over any
ring `A` and proves antisymmetry, self-vanishing, and the general
Jacobiator–associator identity. The Jacobi identity is then proved only on
the associative x-axis coordinate sector. This sector is contained in the
sign-flip fixed locus over every ring; identifying it with the entire fixed
locus additionally requires excluding 2-torsion.

This file makes no associativity claim on the full non-associative algebra — the
commutator is defined for all pairs, but the Jacobi identity holds only on the
associative coordinate-axis sectors (see `AxisFixedSectorLieDerivation`). -/

namespace InfoGeometry.NCG.ZornCommutator

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix

/-- Antisymmetry: `[X, Y] = -[Y, X]` over any noncommutative ring `A`. -/
theorem zornCommutator_antisymm (X Y : OpZornMatrix A) :
    opCommutator X Y = -opCommutator Y X := by
  ext <;>
  simp [opCommutator, sub_eq_add_neg,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale]

/-- Self-commutator vanishes: `[X, X] = 0` over any noncommutative ring `A`. -/
theorem zornCommutator_self (X : OpZornMatrix A) :
    opCommutator X X = 0 := by
  simp [opCommutator]

/-- The Jacobiator of the Zorn commutator measures the failure of the Jacobi
identity on the full non-associative algebra:
`[[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y]`. -/
def zornJacobiator (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  opCommutator (opCommutator X Y) Z +
    opCommutator (opCommutator Y Z) X +
      opCommutator (opCommutator Z X) Y

/-- In any nonassociative ring, the left-nested commutator Jacobiator equals
the alternating sum of the six associators. This records the exact obstruction
to the Jacobi identity on the full Zorn carrier. -/
theorem zornJacobiator_eq_alternating_associator (X Y Z : OpZornMatrix A) :
    zornJacobiator X Y Z =
      opAssociator X Y Z + opAssociator Y Z X + opAssociator Z X Y -
        opAssociator Y X Z - opAssociator Z Y X - opAssociator X Z Y := by
  have h :=
    (universal_akivis_bianchi_identity_and_chiral_volume_commutator
      X Y Z (0 : OpVec3 A) 0 0).1
  change opCommutator (opCommutator X Y) Z +
      opCommutator (opCommutator Y Z) X +
      opCommutator (opCommutator Z X) Y = _
  calc
    _ = opAssociator X Y Z + opAssociator Y Z X + opAssociator Z X Y -
        opAssociator Y X Z - opAssociator X Z Y - opAssociator Z Y X := by
      simpa [opCommutator] using h
    _ = opAssociator X Y Z + opAssociator Y Z X + opAssociator Z X Y -
        opAssociator Y X Z - opAssociator Z Y X - opAssociator X Z Y := by abel

/-- The Jacobiator vanishes on the x-axis Galois-fixed sector `Fix(K_x)`,
where all vectors have only their x-coordinate nonzero. -/
theorem zornJacobiator_vanishes_on_quatSubalgX
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃) = 0 := by
  have h₁ : opAssociator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂) (quatSubalgX a₃ v₃ w₃ b₃) = 0 := by
    ext <;>
    dsimp [quatSubalgX, mul_a, mul_b, mul_v, mul_w, opAssociator,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring
  have h₂ : opAssociator (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃) (quatSubalgX a₁ v₁ w₁ b₁) = 0 := by
    ext <;>
    dsimp [quatSubalgX, mul_a, mul_b, mul_v, mul_w, opAssociator,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring
  have h₃ : opAssociator (quatSubalgX a₃ v₃ w₃ b₃)
      (quatSubalgX a₁ v₁ w₁ b₁) (quatSubalgX a₂ v₂ w₂ b₂) = 0 := by
    ext <;>
    dsimp [quatSubalgX, mul_a, mul_b, mul_v, mul_w, opAssociator,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring
  have h₄ : opAssociator (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₁ v₁ w₁ b₁) (quatSubalgX a₃ v₃ w₃ b₃) = 0 := by
    ext <;>
    dsimp [quatSubalgX, mul_a, mul_b, mul_v, mul_w, opAssociator,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring
  have h₅ : opAssociator (quatSubalgX a₃ v₃ w₃ b₃)
      (quatSubalgX a₂ v₂ w₂ b₂) (quatSubalgX a₁ v₁ w₁ b₁) = 0 := by
    ext <;>
    dsimp [quatSubalgX, mul_a, mul_b, mul_v, mul_w, opAssociator,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring
  have h₆ : opAssociator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₃ v₃ w₃ b₃) (quatSubalgX a₂ v₂ w₂ b₂) = 0 := by
    ext <;>
    dsimp [quatSubalgX, mul_a, mul_b, mul_v, mul_w, opAssociator,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring
  ext <;>
  dsimp [zornJacobiator, opCommutator, quatSubalgX,
    opAssociator,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale,
    h₁, h₂, h₃, h₄, h₅, h₆] <;>
  noncomm_ring

/-- In any distributive, possibly nonassociative ring, the failure of an
inner commutator to be a product derivation is the signed sum of three
associators. This is the exact replacement for the associative Leibniz
identity when associativity is unavailable. -/
theorem nonassoc_commutator_leibniz_defect_eq_associators
    {R : Type*} [NonUnitalNonAssocRing R] (x y z : R) :
    (x * (y * z) - (y * z) * x) -
        ((x * y - y * x) * z + y * (x * z - z * x)) =
      -((x * y) * z - x * (y * z)) +
        ((y * x) * z - y * (x * z)) - ((y * z) * x - y * (z * x)) := by
  simp only [sub_mul, mul_sub]
  abel

/-- The generic defect formula specialized to the actual operator-valued Zorn
product over an arbitrary (possibly noncommutative) coefficient ring. -/
theorem opCommutator_leibniz_defect_eq_associators
    (X Y Z : OpZornMatrix A) :
    opCommutator X (Y * Z) -
        (opCommutator X Y * Z + Y * opCommutator X Z) =
      -opAssociator X Y Z + opAssociator Y X Z - opAssociator Y Z X := by
  simpa [opCommutator, opAssociator] using
    (nonassoc_commutator_leibniz_defect_eq_associators X Y Z)

end InfoGeometry.NCG.ZornCommutator
