import InfoGeometry.Topology.SymbolicLatentVaryingCarrierQuotientCompHaus

/-!
# Indexed compact-Hausdorff quotient/range readout

The varying-carrier quotient and observation-range functors already live in
`CompHaus`.  This owner lifts their natural isomorphism to an arbitrary
indexed diagram.  It deliberately does not assert that a `CompHaus` colimit
is computed by a `TopCat` colimit; that comparison belongs to a separate
colimit owner with the required hypotheses.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]
variable {J : Type} [Category J]

noncomputable def compactIndexedObservationQuotientDiagram
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) : J ⥤ CompHaus :=
  D ⋙ compactSymbolicLatentObservationQuotientCompHausFunctor

noncomputable def compactIndexedObservationRangeDiagram
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) : J ⥤ CompHaus :=
  D ⋙ compactSymbolicLatentObservationRangeCompHausFunctor

noncomputable def compactIndexedObservationQuotientRangeNaturalIso
    (D : J ⥤ CompactSymbolicLatentSystemObject ι) :
    compactIndexedObservationQuotientDiagram D ≅
      compactIndexedObservationRangeDiagram D :=
  NatIso.ofComponents
    (fun j =>
      (compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
        (ι := ι)).app (D.obj j))
    (by
      intro j k f
      exact
        (compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
          (ι := ι)).hom.naturality (D.map f))

theorem compactIndexedObservationQuotientRangeNaturalIso_naturality
    (D : J ⥤ CompactSymbolicLatentSystemObject ι)
    {j k : J} (f : j ⟶ k) :
    (compactIndexedObservationQuotientDiagram D).map f ≫
        (compactIndexedObservationQuotientRangeNaturalIso D).hom.app k =
      (compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
        (compactIndexedObservationRangeDiagram D).map f :=
  (compactIndexedObservationQuotientRangeNaturalIso D).hom.naturality f

@[simp] theorem compactIndexedObservationQuotientRangeNaturalIso_naturality_apply
    (D : J ⥤ CompactSymbolicLatentSystemObject ι)
    {j k : J} (f : j ⟶ k)
    (q : compactSymbolicLatentObservationQuotientCompHaus (D.obj j)) :
    ((compactIndexedObservationQuotientDiagram D).map f ≫
        (compactIndexedObservationQuotientRangeNaturalIso D).hom.app k) q =
      ((compactIndexedObservationQuotientRangeNaturalIso D).hom.app j ≫
        (compactIndexedObservationRangeDiagram D).map f) q := by
  exact congrArg (fun h => h q)
    (compactIndexedObservationQuotientRangeNaturalIso_naturality D f)

end InfoGeometry.Topology
