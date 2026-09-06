import InfoGeometry.Topology.SymbolicLatentQuotientEmbedding

/-!
# Observational quotient as its actual range

Under compactness, the observational quotient is homeomorphic to the range of
the finite observation map.  This is the topological completion of the
quotient/range identification; it still makes no claim that the range is a
manifold or a model of a physical state space.
-/

namespace InfoGeometry.Topology

noncomputable def symbolicObservationQuotientHomeomorphRange
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    _root_.Quotient (symbolicObservationalSetoid S) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) := by
  let Q := _root_.Quotient (symbolicObservationalSetoid S)
  let h₁ : Q ≃ₜ (↑(Set.univ : Set Q)) :=
    (Homeomorph.Set.univ Q).symm
  let h₂ := (symbolicObservationQuotient_isClosedEmbedding S).homeomorphImage
    Set.univ
  let h₃ : (↑(symbolicObservationQuotientMap S '' Set.univ)) ≃ₜ
      (↑(Set.range (symbolicObservationQuotientMap S))) :=
    Homeomorph.setCongr Set.image_univ
  exact h₁.trans (h₂.trans h₃)

@[simp] theorem symbolicObservationQuotientHomeomorphRange_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
  (S : FiniteSymbolicLatentSystem X ι)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    (symbolicObservationQuotientHomeomorphRange S q).1 =
    symbolicObservationQuotientMap S q := by
  dsimp [symbolicObservationQuotientHomeomorphRange]
  rfl

end InfoGeometry.Topology
