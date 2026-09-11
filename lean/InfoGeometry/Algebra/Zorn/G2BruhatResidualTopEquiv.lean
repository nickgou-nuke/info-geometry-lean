import InfoGeometry.Algebra.Zorn.G2CanonicalResidualConcreteBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GroupTheory.G2BruhatInversions

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualTopEquiv

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualConcreteBridge
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.GroupTheory.G2BruhatInversions

/-!
The longest Bruhat parameter is the first concrete residual parameter whose
root-indexed Boolean fiber is transported all the way to the verified
unipotent subgroup.  This composition uses no enumeration of automorphisms.
-/

noncomputable def bruhatTopToCanonical :
    BruhatResidualExponent (3, false) ≃
      CanonicalResidualExponent G2WeylElement.w0 := by
  let hs : bruhatInversionRoots (3, false) =
      dihedralInversionRoots (3, false) := by
    rw [bruhatInversionRoots, dihedralInversionRoots_eq_canonicalSigned]
  let sourceEquiv :
      {α : G2PositiveRoot // α ∈ bruhatInversionRoots (3, false)} ≃
        {α : G2PositiveRoot // α ∈ dihedralInversionRoots (3, false)} :=
    { toFun := fun α => ⟨α.1, by rw [← hs]; exact α.2⟩
      invFun := fun α => ⟨α.1, by rw [hs]; exact α.2⟩
      left_inv := by intro α; rfl
      right_inv := by intro α; rfl }
  let targetEquiv :
      {α : G2PositiveRoot //
          α ∈ canonicalSignedInversionRoots (weylElementOfNF (3, false))} ≃
        {α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots G2WeylElement.w0} :=
    { toFun := fun α => ⟨α.1, by simp at α ⊢⟩
      invFun := fun α => ⟨α.1, by simp at α ⊢⟩
      left_inv := by intro α; rfl
      right_inv := by intro α; rfl }
  exact ((sourceEquiv.arrowCongr (Equiv.refl Bool)).trans
    ((residualRootEquiv (3, false)).arrowCongr (Equiv.refl Bool))).trans
      (targetEquiv.arrowCongr (Equiv.refl Bool))

noncomputable def bruhatTopResidualSubgroupEquiv :
    BruhatResidualExponent (3, false) ≃
      {x : SplitOctF2Aut // x ∈ residualSubgroup (3, false)} :=
  bruhatTopToCanonical.trans canonicalW0ResidualSubgroupEquiv

theorem bruhatTopResidualSubgroup_card :
    Nat.card (BruhatResidualExponent (3, false)) =
      Nat.card (residualSubgroup (3, false)) :=
  Nat.card_congr bruhatTopResidualSubgroupEquiv

theorem bruhatTopResidualSubgroup_card_eq_64 :
    Nat.card (BruhatResidualExponent (3, false)) = 64 := by
  rw [bruhatTopResidualSubgroup_card]
  exact residualSubgroup_top_parameter_card

end InfoGeometry.Algebra.Zorn.G2BruhatResidualTopEquiv
