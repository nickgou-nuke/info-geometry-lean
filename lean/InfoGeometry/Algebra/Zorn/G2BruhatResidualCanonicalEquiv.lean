import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GroupTheory.G2BruhatInversions
import InfoGeometry.Algebra.Zorn.G2ReducedWords

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualCanonicalEquiv

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.GroupTheory.G2BruhatInversions

/-!
Carrier alignment for the Boolean residual coordinates.  This theorem only
identifies the root-indexed coordinate types; it deliberately does not claim
that the coordinates already form a concrete subgroup.
-/

noncomputable def bruhatResidualToCanonical
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    BruhatResidualExponent p ≃
      CanonicalResidualExponent (weylElementOfNF p) := by
  let hroot : bruhatInversionRoots p = dihedralInversionRoots p := by
    rw [bruhatInversionRoots, dihedralInversionRoots_eq_canonicalSigned]
  let sourceEquiv :
      {α : G2PositiveRoot // α ∈ bruhatInversionRoots p} ≃
        {α : G2PositiveRoot // α ∈ dihedralInversionRoots p} :=
    { toFun := fun α => ⟨α.1, by rw [← hroot]; exact α.2⟩
      invFun := fun α => ⟨α.1, by rw [hroot]; exact α.2⟩
      left_inv := by intro α; rfl
      right_inv := by intro α; rfl }
  exact (sourceEquiv.arrowCongr (Equiv.refl Bool)).trans
    (residualRootEquiv p |>.arrowCongr (Equiv.refl Bool))

theorem bruhatResidualToCanonical_card
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    Nat.card (BruhatResidualExponent p) =
      Nat.card (CanonicalResidualExponent (weylElementOfNF p)) :=
  Nat.card_congr (bruhatResidualToCanonical p)

theorem bruhatResidualToCanonical_card_eq_pow
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    Nat.card (BruhatResidualExponent p) = 2 ^ dihedralLength p := by
  rw [bruhatResidualToCanonical_card]
  rw [Nat.card_eq_fintype_card, canonicalResidualExponent_card,
    weylElementOfNF_length]

end InfoGeometry.Algebra.Zorn.G2BruhatResidualCanonicalEquiv
