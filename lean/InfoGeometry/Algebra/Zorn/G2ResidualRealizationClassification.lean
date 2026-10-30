import InfoGeometry.Algebra.Zorn.G2ResidualExponentRealizationBoundary
import InfoGeometry.Algebra.Zorn.G2CorrectedResidualCard

/-!
# Exact boundary of uncorrected residual exponent cardinalities

Contract: classify the existing predicate `ResidualExponentRealizes`, which
asks only for a set equivalence with the actual native residual subgroup.
The native residual cardinality uses correctedLength, while the uncorrected
inversion carrier uses dihedralLength. Finite cardinality comparison therefore
decides this predicate for all twelve parameters. This does not supply an
ordered root-product map or a group isomorphism.
-/
namespace InfoGeometry.Algebra.Zorn.G2ResidualRealizationClassification

open G2ResidualExponentRealizationBoundary G2CorrectedResidualCard
open G2CorrectedWordLength G2ReducedWords G2BruhatResidual
open G2TwoBruhatClassification
open InfoGeometry.GroupTheory.G2BruhatInversions

theorem realizes_iff_lengths_equal (p : WeylG2) :
    ResidualExponentRealizes p ↔ correctedLength p = dihedralLength p := by
  constructor
  · intro h
    have hc := residualExponentRealizes_card p h
    rw [residual_card] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hc
  · intro h
    letI : Fintype (residualSubgroup p) := Fintype.ofFinite _
    apply Fintype.card_eq.mp
    rw [bruhatResidualExponent_card]
    have hc := residual_card p
    rw [Nat.card_eq_fintype_card, h] at hc
    exact hc.symm

theorem length_agreement_classification : ∀ p : WeylG2,
    (correctedLength p = dihedralLength p) ↔
      p.2 = false ∨ p.1 = 0 ∨ p.1 = 3 := by
  decide

/-- Eight parameters admit a set equivalence; the four remaining reflections
have different source and target cardinalities. -/
theorem realizes_iff_parameter (p : WeylG2) :
    ResidualExponentRealizes p ↔ p.2 = false ∨ p.1 = 0 ∨ p.1 = 3 := by
  rw [realizes_iff_lengths_equal, length_agreement_classification]

end InfoGeometry.Algebra.Zorn.G2ResidualRealizationClassification
