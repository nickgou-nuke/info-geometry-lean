import InfoGeometry.Canonical.Spin44CharacterShadow
import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

/-!
Direct theorem projections for the finite character, KKT, and split-Clifford
owners imported above.  Classification/status vectors are intentionally not
represented as Lean evidence; each claim remains an explicit proposition with
its actual owner theorem.
-/

namespace InfoGeometry.Canonical.TheoryShadow

open scoped BigOperators
open scoped InnerProductSpace

open InfoGeometry.Canonical.Spin44CharacterShadow
open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
open InfoGeometry.Canonical.SouriauLieThermoKKTBridge
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

theorem exactKKT_translator_shadow_packet
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α))
    (hPSD : (souriauFisherResponseMatrix C.M C.T).PositiveSemidefinite)
    (eta xβ xμ : ℝ) :
    (DimensionAgnosticKKTResiduals.exact.toShadow).coneAdmissible ∧
      (DimensionAgnosticKKTResiduals.exact.toShadow).stationarity ∧
      (DimensionAgnosticKKTResiduals.exact.toShadow).complementarySlackness ∧
      (DimensionAgnosticKKTResiduals.exact.toShadow).finitePartitionAdmissible := by
  have out := structuredSouriauKKTTranslatorPacket_ofExactWitness
    (C := C) hPSD eta xβ xμ
  exact out.2

theorem splitCl44_TKK_shadow_bridge_packet
    [Fintype α] [Nonempty α]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (P : SplitCl44TKKJordanLiePacket (α := α) (H := H))
    (x : ℝ × ℝ)
    (xs : InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNCarrier 3) :
    P.closure.gibbs.SatisfiesOperatorTKKMasterRelation P.closure.tkkParameter ∧
      P.closure.gibbs.IsOperatorAdmissible ∧
      P.triality.informationalDiracSquare = LinearMap.id := by
  have h := P.splitCl44_TKK_JordanLie_constructive_packet x xs
  refine ⟨?_, ?_, ?_⟩
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.1

end InfoGeometry.Canonical.TheoryShadow
