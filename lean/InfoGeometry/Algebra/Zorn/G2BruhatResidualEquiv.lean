import InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
import InfoGeometry.GroupTheory.G2BruhatInversions

/-!
# Ordered inversion coordinates for Bruhat residual fibers

This owner provides only the finite ordering interface.  It deliberately does
not identify Boolean coordinates with a concrete residual subgroup: that
requires an ordered root-subgroup product and separate injectivity and
surjectivity proofs.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv

open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.GroupTheory.G2BruhatInversions
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
open InfoGeometry.Algebra.Zorn.G2CorrectedTComplementCard
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

abbrev ZeroBitPCExponent := {e : PCExponent // e 0 = false}

/-- Concrete parametrization of the corrected simple residual subgroup.
This is intentionally a five-free-bit PC parametrization, not an inversion-root
parametrization: the latter has cardinality eight for this Weyl parameter. -/
noncomputable def correctedSimpleResidualEquiv :
    ZeroBitPCExponent ≃ residualSubgroup (2, true) := by
  let f : ZeroBitPCExponent → residualSubgroup (2, true) := fun e =>
    ⟨G2TwoSylowSubgroup.pcWord e.1, by
      rw [residualSubgroup_simple_eq_correctedTComplementSubgroup]
      exact pcWord_mem_correctedTComplement e.1 e.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    apply pcWord_injective
    exact congrArg Subtype.val h
  · intro x
    rw [residualSubgroup_simple_eq_correctedTComplementSubgroup] at x
    rcases x.2 with ⟨e, he, hxe⟩
    refine ⟨⟨e, he⟩, ?_⟩
    apply Subtype.ext
    exact hxe

/-- Canonical ordering of the inversion-root subtype. -/
noncomputable def orderedInversionRoots (p : WeylG2) :
    Fin (dihedralLength p) ≃
      { α : G2PositiveRoot // α ∈ bruhatInversionRoots p } :=
  (Finite.equivFinOfCardEq
      (by
        simp [Nat.card_eq_fintype_card, bruhatInversionRoots_card p])).symm

@[simp]
theorem orderedInversionRoots_apply (p : WeylG2)
    (i : Fin (dihedralLength p)) :
    (orderedInversionRoots p i).1 ∈ bruhatInversionRoots p :=
  (orderedInversionRoots p i).2

theorem orderedInversionRoots_bijective (p : WeylG2) :
    Function.Bijective (orderedInversionRoots p) :=
  (orderedInversionRoots p).bijective

end InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv
