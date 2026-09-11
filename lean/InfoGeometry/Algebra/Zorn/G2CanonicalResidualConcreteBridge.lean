/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-!
# Concrete bridge for the longest residual cell

For the longest Weyl element all six positive roots are inverted.  The
canonical Boolean residual coordinates therefore compose directly with the
verified six-bit PC-word equivalence onto the concrete unipotent subgroup.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualConcreteBridge

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def pcWordPlainEquiv :
    (Fin 6 → Bool) ≃ unipotentSubgroup where
  toFun e :=
    ⟨G2TwoSylowSubgroup.pcWord e, ⟨e, rfl⟩⟩
  invFun u := Classical.choose u.2
  left_inv e := by
    have h := Classical.choose_spec
      (⟨G2TwoSylowSubgroup.pcWord e, ⟨e, rfl⟩⟩ : unipotentSubgroup).2
    exact G2TwoPCRecoveryTransport.pcWord_injective_concrete h
  right_inv u := by
    ext
    exact Classical.choose_spec u.2

noncomputable def canonicalW0ResidualEquiv :
    CanonicalResidualExponent G2WeylElement.w0 ≃ unipotentSubgroup :=
  (canonicalResidualBinaryEquiv G2WeylElement.w0).trans
    pcWordPlainEquiv

theorem canonicalW0ResidualEquiv_card :
    Nat.card (CanonicalResidualExponent G2WeylElement.w0) =
      Nat.card unipotentSubgroup := by
  exact Nat.card_congr canonicalW0ResidualEquiv

theorem canonicalW0ResidualEquiv_target_card :
    Fintype.card (CanonicalResidualExponent G2WeylElement.w0) = 64 := by
  rw [canonicalResidualExponent_card]
  rfl

noncomputable def canonicalW0ResidualSubgroupEquiv :
    CanonicalResidualExponent G2WeylElement.w0 ≃
      { x : SplitOctF2Aut // x ∈ residualSubgroup (3, false) } := by
  let hsub : unipotentSubgroup = residualSubgroup (3, false) :=
    residualSubgroup_top_parameter.symm
  let carrierEquiv : unipotentSubgroup ≃
      { x : SplitOctF2Aut // x ∈ residualSubgroup (3, false) } :=
    { toFun := fun x => ⟨x.1, by rw [← hsub]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [hsub]; exact x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact canonicalW0ResidualEquiv.trans carrierEquiv

theorem canonicalW0ResidualSubgroupEquiv_card :
    Nat.card (CanonicalResidualExponent G2WeylElement.w0) =
      Nat.card (residualSubgroup (3, false)) := by
  exact Nat.card_congr canonicalW0ResidualSubgroupEquiv

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualConcreteBridge
