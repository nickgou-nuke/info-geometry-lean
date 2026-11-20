/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
import InfoGeometry.Canonical.ZornMatrixVectorCarrierBridge
import InfoGeometry.Canonical.SplitOctonionMalcevIdentity
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge

/-!
# Real carrier bridge for Peirce supercolor and the circular Zorn owners

The Peirce supercolor owner presents split Zorn multiplication on
`ZornAlgebra ℝ`; the canonical owner presents the same eight coordinates as
`ZornMatrix ℝ`.  This file composes their existing coordinate equivalences and
checks multiplication against both native products.  It does not identify
their chosen color/root basis vectors or turn either nonassociative carrier
into an associative matrix algebra.
-/

namespace InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge

open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra
open InfoGeometry.Canonical
open InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCircularCAR

local notation "SZ" => ZornAlgebra ℝ
local notation "CZ" => ZornMatrix ℝ

private theorem supercolorMap_add (X Y : SZ) :
    equivZornVectorMatrix (ZornAlgebra.add X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.add
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y) := by
  ext i
  · rfl
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

private theorem supercolorMap_sub (X Y : SZ) :
    equivZornVectorMatrix (ZornAlgebra.sub X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.sub
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y) := by
  ext i
  · rfl
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

/-- The existing Peirce supercolor carrier, converted to the canonical real
Zorn coordinate carrier through the two owner linear equivalences. -/
def supercolorToCanonicalZorn : SZ ≃ₗ[ℝ] CZ :=
  (equivZornVectorMatrix (R := ℝ)).trans
    (zornMatrixVectorLinearEquiv (R := ℝ)).symm

/-- The inverse coordinate conversion. -/
def canonicalZornToSupercolor : CZ ≃ₗ[ℝ] SZ :=
  supercolorToCanonicalZorn.symm

@[simp] theorem canonicalZornToSupercolor_supercolor (X : SZ) :
    canonicalZornToSupercolor (supercolorToCanonicalZorn X) = X :=
  supercolorToCanonicalZorn.symm_apply_apply X

@[simp] theorem supercolorToCanonicalZorn_canonical (X : CZ) :
    supercolorToCanonicalZorn (canonicalZornToSupercolor X) = X :=
  supercolorToCanonicalZorn.apply_symm_apply X

/-- The carrier conversion preserves the native nonassociative Zorn product.
The proof composes the supercolor owner's product theorem with the canonical
Zorn coordinate multiplication theorem. -/
theorem supercolorToCanonicalZorn_mul (X Y : SZ) :
    supercolorToCanonicalZorn (ZornAlgebra.mul X Y) =
      ZornMatrix.mul (supercolorToCanonicalZorn X)
        (supercolorToCanonicalZorn Y) := by
  apply (zornMatrixVectorLinearEquiv (R := ℝ)).injective
  simpa [supercolorToCanonicalZorn, zornMatrixToVector_mul,
    zornMatrixToVector_toMatrix] using
    equivZornVectorMatrix_mul X Y

/-- The canonical split-octonion carrier can be recovered from the real
Peirce supercolor coordinates without changing the multiplication convention. -/
theorem canonicalZorn_mul_via_supercolor (X Y : CZ) :
    supercolorToCanonicalZorn
        (ZornAlgebra.mul (canonicalZornToSupercolor X)
          (canonicalZornToSupercolor Y)) = ZornMatrix.mul X Y := by
  rw [supercolorToCanonicalZorn_mul]
  simp

/-- Compose the Peirce-supercolor coordinate map with the existing real
Zorn-to-doubled-Krein equivalence. This is a linear carrier equivalence; the
indefinite pairing and grading remain those of the H4 owner. -/
noncomputable def supercolorToDoubleKrein : SZ ≃ₗ[ℝ] H4 :=
  supercolorToCanonicalZorn.trans zornToDoubleKrein

@[simp] theorem supercolorToDoubleKrein_apply (X : SZ) :
    supercolorToDoubleKrein X = zornToDoubleKrein (supercolorToCanonicalZorn X) := rfl

/-- Multiplication by a supercolor element, transported to H4, acts by the
existing doubled-Krein right-regular operator. This records the order of
factors explicitly and makes no associativity claim. -/
theorem supercolor_rightRegular_action (X Y : SZ) :
    supercolorToDoubleKrein (ZornAlgebra.mul Y X) =
      rightRegularOnDoubleKrein (supercolorToCanonicalZorn X)
        (supercolorToDoubleKrein Y) := by
  rw [supercolorToDoubleKrein_apply, supercolorToDoubleKrein_apply,
    supercolorToCanonicalZorn_mul, rightRegularOnDoubleKrein_apply,
    zornToDoubleKrein.symm_apply_apply]
  rfl

/-! ### Jordan and Malcev laws transported from the owner algebra

The carrier equivalence above preserves the nonassociative product.  Thus
symmetrization and the Malcev defect transfer by explicit product-respecting
equalities; these results do not regard Zorn multiplication as matrix
multiplication. -/

/-- The supercolor anticommutator is carried to the split-octonion Jordan
product on the canonical vector-matrix carrier. -/
theorem supercolor_anticommutator_eq_canonical_jordan (X Y : SZ) :
    equivZornVectorMatrix (ZornAlgebra.anticommutator X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.zornJordan
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y) := by
  change equivZornVectorMatrix (ZornAlgebra.mul X Y + ZornAlgebra.mul Y X) = _
  rw [show ZornAlgebra.mul X Y + ZornAlgebra.mul Y X =
      ZornAlgebra.add (ZornAlgebra.mul X Y) (ZornAlgebra.mul Y X) by rfl,
    supercolorMap_add, equivZornVectorMatrix_mul, equivZornVectorMatrix_mul]
  rfl

/-- The Jordan identity for the supercolor anticommutator is the split-
octonion Jordan identity transported through the owner equivalence. -/
theorem supercolor_jordan_identity (X Y : SZ) :
    ZornAlgebra.anticommutator
        (ZornAlgebra.anticommutator
          (ZornAlgebra.anticommutator X X) Y) X =
      ZornAlgebra.anticommutator
        (ZornAlgebra.anticommutator X X)
        (ZornAlgebra.anticommutator Y X) := by
  apply equivZornVectorMatrix.injective
  simpa only [supercolor_anticommutator_eq_canonical_jordan] using
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_jordan_von_neumann_wigner_1934_axiom_III_and_peirce
    (equivZornVectorMatrix X) (equivZornVectorMatrix Y) (equivZornVectorMatrix X)
    (0 : InfoGeometry.Algebra.ZornVec3 ℝ) (0 : InfoGeometry.Algebra.ZornVec3 ℝ)).2.2.2.1

/-- Cyclic Jacobiator of the commutator formed from the supercolor owner's
nonassociative product. -/
def supercolorCommutatorJacobiator (X Y Z : SZ) : SZ :=
  ZornAlgebra.add
    (ZornAlgebra.commutator X (ZornAlgebra.commutator Y Z))
    (ZornAlgebra.add
      (ZornAlgebra.commutator Y (ZornAlgebra.commutator Z X))
      (ZornAlgebra.commutator Z (ZornAlgebra.commutator X Y)))

private theorem supercolorCommutator_to_canonical (X Y : SZ) :
    equivZornVectorMatrix (ZornAlgebra.commutator X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.commutator
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y) := by
  unfold ZornAlgebra.commutator InfoGeometry.Algebra.ZornVectorMatrix.commutator
  rw [supercolorMap_sub, equivZornVectorMatrix_mul, equivZornVectorMatrix_mul]

private theorem supercolorJacobiator_to_canonical (X Y Z : SZ) :
    equivZornVectorMatrix (supercolorCommutatorJacobiator X Y Z) =
      InfoGeometry.Algebra.ZornVectorMatrix.commutatorJacobiator
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y)
        (equivZornVectorMatrix Z) := by
  unfold supercolorCommutatorJacobiator
  unfold InfoGeometry.Algebra.ZornVectorMatrix.commutatorJacobiator
  rw [supercolorMap_add, supercolorMap_add,
    supercolorCommutator_to_canonical, supercolorCommutator_to_canonical,
    supercolorCommutator_to_canonical, supercolorCommutator_to_canonical,
    supercolorCommutator_to_canonical, supercolorCommutator_to_canonical]

/-- The full Malcev defect formed with the supercolor Zorn product maps to
the canonical `ZornVectorMatrix` Malcev defect. The products are kept in
their displayed order. -/
def supercolorMalcevDefect (X Y Z : SZ) : SZ :=
  ZornAlgebra.sub
    (supercolorCommutatorJacobiator X Y (ZornAlgebra.commutator X Z))
    (ZornAlgebra.commutator (supercolorCommutatorJacobiator X Y Z) X)

/-- Product-respecting carrier equivalence transports the supercolor Malcev
defect to the owner defect without changing its associator convention. -/
theorem supercolorMalcevDefect_to_canonical (X Y Z : SZ) :
    equivZornVectorMatrix (supercolorMalcevDefect X Y Z) =
      InfoGeometry.Algebra.ZornVectorMatrix.malcevDefect
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y)
        (equivZornVectorMatrix Z) := by
  unfold supercolorMalcevDefect
  rw [supercolorMap_sub,
    supercolorJacobiator_to_canonical X Y (ZornAlgebra.commutator X Z),
    supercolorCommutator_to_canonical (supercolorCommutatorJacobiator X Y Z) X,
    supercolorJacobiator_to_canonical X Y Z,
    supercolorCommutator_to_canonical X Z]
  unfold InfoGeometry.Algebra.ZornVectorMatrix.malcevDefect
  rfl

/-- The Peirce supercolor carrier satisfies the Malcev identity because its
explicit product is multiplicatively equivalent to the canonical split-
octonion vector-matrix product. -/
theorem supercolor_malcev_identity (X Y Z : SZ) :
    supercolorMalcevDefect X Y Z = 0 := by
  apply equivZornVectorMatrix.injective
  rw [supercolorMalcevDefect_to_canonical]
  have hzero : equivZornVectorMatrix (0 : SZ) =
      InfoGeometry.Algebra.ZornVectorMatrix.zero := by
    apply InfoGeometry.Algebra.ZornVectorMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  exact (InfoGeometry.Algebra.ZornVectorMatrix.malcev_identity
    (R := ℝ) (equivZornVectorMatrix X) (equivZornVectorMatrix Y)
      (equivZornVectorMatrix Z)).trans hzero.symm


end InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
