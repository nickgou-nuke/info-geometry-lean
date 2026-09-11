import InfoGeometry.Topology.SymbolicLatentObservationRangeFlowCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# CompHaus composition law for the observational range flow

The range-flow owner already proves the cocycle at the homeomorphism level.
This file exposes the same law for the corresponding `CompHaus` morphisms.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_comp
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (s t : ℝ) :
    Φ.observationQuotientRangeFlowCompHausHom S h_cont s ≫
        Φ.observationQuotientRangeFlowCompHausHom S h_cont t =
      Φ.observationQuotientRangeFlowCompHausHom S h_cont (t + s) := by
  apply ConcreteCategory.hom_ext
  intro q
  change
    (Φ.observationQuotientRangeFlowHomeomorph S h_cont s).trans
        (Φ.observationQuotientRangeFlowHomeomorph S h_cont t) q =
      Φ.observationQuotientRangeFlowHomeomorph S h_cont (t + s) q
  exact Φ.observationQuotientRangeFlowHomeomorph_comp_apply S h_cont s t q

end InfoGeometry.Topology
