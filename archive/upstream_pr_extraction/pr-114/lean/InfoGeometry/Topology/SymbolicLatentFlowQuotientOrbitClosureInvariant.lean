import InfoGeometry.Topology.SymbolicLatentFlowQuotientTransportOrbitClosure

namespace InfoGeometry.Topology

/-!
# Flow invariance of symbolic latent orbit closures

The preceding owner proves transport of orbit closures under each quotient
flow homeomorphism.  This owner extracts the intrinsic consequence: changing
the base point along its orbit does not change the orbit closure.  No
recurrence, minimality, ergodicity, or measure-theoretic statement is used.
-/

noncomputable section

theorem rangeFlowOrbit_subset_rangeFlowOrbit_flow
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowOrbit F (rangeFlowAct F s y) ⊆ rangeFlowOrbit F y := by
  rintro z ⟨t, rfl⟩
  refine ⟨t + s, ?_⟩
  exact rangeFlowAct_add F t s y

theorem rangeFlowOrbit_flow_subset_rangeFlowOrbit
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowOrbit F y ⊆ rangeFlowOrbit F (rangeFlowAct F s y) := by
  rintro z ⟨t, rfl⟩
  refine ⟨t - s, ?_⟩
  change rangeFlowAct F (t - s) (rangeFlowAct F s y) =
    rangeFlowAct F t y
  rw [← rangeFlowAct_add]
  congr 1
  ring

theorem rangeFlowOrbitClosure_flow_invariant
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowOrbitClosure F (rangeFlowAct F s y) =
      rangeFlowOrbitClosure F y := by
  apply Set.Subset.antisymm
  · unfold rangeFlowOrbitClosure
    exact closure_mono (rangeFlowOrbit_subset_rangeFlowOrbit_flow F s y)
  · unfold rangeFlowOrbitClosure
    exact closure_mono (rangeFlowOrbit_flow_subset_rangeFlowOrbit F s y)

end
end InfoGeometry.Topology
