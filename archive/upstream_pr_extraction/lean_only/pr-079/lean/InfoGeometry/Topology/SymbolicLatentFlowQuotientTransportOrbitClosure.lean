import Mathlib
import InfoGeometry.Topology.SymbolicLatentFlowQuotientTransport
import InfoGeometry.Topology.SymbolicLatentObservationQuotientTopCat

namespace InfoGeometry.Topology

/-!
# Orbit and orbit-closure transport for the finite symbolic latent flow

The quotient/range flow owner gives a homeomorphism at every time.  Here we
record the resulting orbit covariance and closure covariance on the closed
observational image.  No recurrence, minimality, ergodicity, or compactness
claim is inferred from these identities.
-/

noncomputable section

def rangeFlowOrbit
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (y : Set.range (symbolicObservationQuotientMap S)) : Set
      (Set.range (symbolicObservationQuotientMap S)) :=
  Set.range (fun t : ℝ => rangeFlowAct F t y)

def rangeFlowOrbitClosure
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (y : Set.range (symbolicObservationQuotientMap S)) : Set
      (Set.range (symbolicObservationQuotientMap S)) :=
  closure (rangeFlowOrbit F y)

theorem rangeFlowOrbit_subset_orbitClosure
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowOrbit F y ⊆ rangeFlowOrbitClosure F y :=
  subset_closure

theorem rangeFlowOrbitClosure_isClosed
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    IsClosed (rangeFlowOrbitClosure F y) :=
  isClosed_closure

theorem rangeFlowOrbitClosure_isCompact
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    IsCompact (rangeFlowOrbitClosure F y) := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  exact (rangeFlowOrbitClosure_isClosed F y).isCompact

theorem rangeFlowHomeomorph_image_orbit
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowHomeomorph F s '' rangeFlowOrbit F y =
      rangeFlowOrbit F (rangeFlowAct F s y) := by
  ext z
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    rw [rangeFlowHomeomorph_apply]
    change rangeFlowAct F t (rangeFlowAct F s y) =
      rangeFlowAct F s (rangeFlowAct F t y)
    calc
      rangeFlowAct F t (rangeFlowAct F s y) =
          rangeFlowAct F (t + s) y := (rangeFlowAct_add F t s y).symm
      _ = rangeFlowAct F s (rangeFlowAct F t y) := by
        simpa [add_comm] using rangeFlowAct_add F s t y
  · rintro ⟨t, rfl⟩
    refine ⟨rangeFlowAct F t y, ⟨t, rfl⟩, ?_⟩
    rw [rangeFlowHomeomorph_apply]
    change rangeFlowAct F s (rangeFlowAct F t y) =
      rangeFlowAct F t (rangeFlowAct F s y)
    calc
      rangeFlowAct F s (rangeFlowAct F t y) =
          rangeFlowAct F (s + t) y := (rangeFlowAct_add F s t y).symm
      _ = rangeFlowAct F t (rangeFlowAct F s y) := by
        simpa [add_comm] using rangeFlowAct_add F t s y

theorem rangeFlowHomeomorph_image_orbitClosure
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowHomeomorph F s '' rangeFlowOrbitClosure F y =
      rangeFlowOrbitClosure F (rangeFlowAct F s y) := by
  rw [rangeFlowOrbitClosure, rangeFlowOrbitClosure]
  rw [(rangeFlowHomeomorph F s).image_closure]
  exact congrArg closure (rangeFlowHomeomorph_image_orbit F s y)

end
end InfoGeometry.Topology
