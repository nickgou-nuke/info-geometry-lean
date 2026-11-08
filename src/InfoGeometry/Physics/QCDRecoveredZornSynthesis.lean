import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.QCDNativeZornColorRepresentation
import InfoGeometry.Physics.QCDCanonicalComplexZornBridge
import InfoGeometry.Physics.QCDZornCl55FureyBridge

/-!
# Recovered Zorn synthesis capstone

The deep-search recovery closes two complementary Zorn corridors:

* over `ℂ`: a faithful `gl₃(ℂ)` action on the three-component color lane,
  injectively realized in the complex Zorn upper slot, together with an exact
  product-preserving equivalence between the canonical complex Zorn carrier and
  the braid/conjugation Zorn carrier;
* over `ℝ`: an injective map from the full canonical real circular Zorn carrier
  into `Cl(5,5)`, with the three color generators landing in the conjugate
  Furey span.

The scalar fields are deliberately not conflated.  A complexified
Zorn-to-`Cl(5,5)` intertwiner remains a separate construction problem.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDRecoveredZornSynthesis

open InfoGeometry.Physics.QCDNativeZornColorRepresentation
open InfoGeometry.Physics.QCDCanonicalComplexZornBridge
open InfoGeometry.Physics.QCDZornCl55FureyBridge

/-- Complex recovered-Zorn packet: faithful color action plus exact canonical
carrier transport. -/
theorem complex_recovered_zorn_packet :
    Function.Injective colorAction ∧
    Function.Injective upperLaneEmbedding ∧
    Function.Bijective canonicalComplexEquiv ∧
    (∀ X Y : CanonicalZorn,
      canonicalComplexEquiv
          (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X Y) =
        InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
          (canonicalComplexEquiv X) (canonicalComplexEquiv Y)) := by
  exact ⟨colorAction_injective,
    upperLaneEmbedding_injective,
    canonicalComplexEquiv.bijective,
    canonicalComplexEquiv_mul⟩

/-- Real recovered-Zorn packet: full carrier injection into `Cl(5,5)` and
color-generator landing in the conjugate Furey span. -/
theorem real_zorn_clifford_furey_packet :
    Function.Injective canonicalZornToCl55 ∧
    (∀ i : Fin 3,
      canonicalZornToCl55 (canonicalColorGenerator i) ∈
        InfoGeometry.Physics.ColorCARStandardModel.fureyConjugateGeneration) := by
  exact ⟨canonicalZornToCl55_injective,
    canonicalColorGenerator_mem_fureyConjugateGeneration⟩

/-- Full recovered-Zorn dependency capstone, keeping complex and real carriers
explicitly separate. -/
theorem recovered_zorn_synthesis_packet :
    Function.Injective colorAction ∧
    Function.Bijective canonicalComplexEquiv ∧
    Function.Injective canonicalZornToCl55 ∧
    (∀ i : Fin 3,
      canonicalZornToCl55 (canonicalColorGenerator i) ∈
        InfoGeometry.Physics.ColorCARStandardModel.fureyConjugateGeneration) := by
  exact ⟨colorAction_injective,
    canonicalComplexEquiv.bijective,
    canonicalZornToCl55_injective,
    canonicalColorGenerator_mem_fureyConjugateGeneration⟩

end InfoGeometry.Physics.QCDRecoveredZornSynthesis

end noncomputable section
