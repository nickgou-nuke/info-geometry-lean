import InfoGeometry.Topology.SymbolicLatentObservationRangeReversalMorphismBridge
import InfoGeometry.Topology.SymbolicLatentObservationRangeFlowMorphismBridge

/-!
# Morphism-level flow/reversal naturality

When concrete symbolic morphisms property the quotient flow and reversal maps,
the already established CompHaus flow/reversal law transports to their
observation-range readouts.  The property hypotheses are explicit: this file
does not manufacture latent morphisms from quotient actions.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem symbolicObservationRangeCompHausHomOfMorphism_flow_reversal
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (t : ℝ)
    (F_t F_R F_neg : SymbolicLatentMorphism S S)
    (h_t : ∀ q, F_t.quotientMap q =
      descendedSymbolicLatentObservationFlow Φ t q)
    (h_R : ∀ q, F_R.quotientMap q =
      descendedSymbolicLatentObservationInvolution R q)
    (h_neg : ∀ q, F_neg.quotientMap q =
      descendedSymbolicLatentObservationFlow Φ (-t) q) :
    symbolicObservationRangeCompHausHomOfMorphism F_t ≫
        symbolicObservationRangeCompHausHomOfMorphism F_R =
      symbolicObservationRangeCompHausHomOfMorphism F_R ≫
        symbolicObservationRangeCompHausHomOfMorphism F_neg := by
  rw [symbolicObservationRangeCompHausHomOfMorphism_eq_flow
      Φ h_flow t F_t h_t]
  rw [symbolicObservationRangeCompHausHomOfMorphism_eq_reversal
      R h_cont F_R h_R]
  rw [symbolicObservationRangeCompHausHomOfMorphism_eq_flow
      Φ h_flow (-t) F_neg h_neg]
  exact SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom_flow_reversal
    R h_flow h_cont t

end InfoGeometry.Topology

end
