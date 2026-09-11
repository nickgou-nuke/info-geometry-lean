/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

/-!
# Concrete longest-cell product-image equivalence

The canonical residual PC-word map is already proved injective.  At the
longest Weyl element its source and the verified unipotent subgroup both have
cardinality 64, so finite cardinality upgrades that map to an equivalence.
This is a concrete PC-carrier result; it does not assert a general ordered
Chevalley product theorem or Bruhat coverage.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCEquiv

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem canonicalResidualPCWord_mem_unipotent
    (e : CanonicalResidualExponent G2WeylElement.w0) :
    canonicalResidualPCWord G2WeylElement.w0 e ∈ unipotentSubgroup := by
  rw [← sylowTwoSubgroup_eq_unipotentSubgroup,
    ← pcSubgroup_eq_sylowTwoSubgroup]
  exact canonicalResidualPCWord_mem_pcSubgroup _ _

noncomputable def canonicalW0PCWordToUnipotent :
    CanonicalResidualExponent G2WeylElement.w0 → unipotentSubgroup :=
  fun e => ⟨canonicalResidualPCWord G2WeylElement.w0 e,
    canonicalResidualPCWord_mem_unipotent e⟩

theorem canonicalW0PCWordToUnipotent_injective :
    Function.Injective canonicalW0PCWordToUnipotent := by
  intro e₁ e₂ h
  apply canonicalResidualPCWord_injective G2WeylElement.w0
  exact congrArg Subtype.val h

theorem canonicalW0PCWordToUnipotent_bijective :
    Function.Bijective canonicalW0PCWordToUnipotent := by
  letI : Fintype unipotentSubgroup := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact canonicalW0PCWordToUnipotent_injective
  · calc
      Fintype.card (CanonicalResidualExponent G2WeylElement.w0) = 64 := by
        rw [canonicalResidualExponent_card]
        rfl
      _ = Fintype.card unipotentSubgroup := by
        symm
        simpa [Nat.card_eq_fintype_card] using unipotentSubgroup_card

noncomputable def canonicalW0PCWordEquiv :
    CanonicalResidualExponent G2WeylElement.w0 ≃ unipotentSubgroup :=
  Equiv.ofBijective canonicalW0PCWordToUnipotent
    canonicalW0PCWordToUnipotent_bijective

theorem canonicalW0PCWordEquiv_card :
    Nat.card (CanonicalResidualExponent G2WeylElement.w0) =
      Nat.card unipotentSubgroup :=
  Nat.card_congr canonicalW0PCWordEquiv

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCEquiv
