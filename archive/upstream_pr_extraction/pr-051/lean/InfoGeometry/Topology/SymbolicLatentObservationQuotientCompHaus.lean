import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of the observational quotient

For a compact latent carrier, the observational quotient is homeomorphic to
the compact feature-readout range.  This owner transports that existing
homeomorphism into `CompHaus`; it does not introduce a second quotient.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι : Type} [TopologicalSpace X] [CompactSpace X] [Fintype ι]

private noncomputable def quotientRangeHomeomorph
    (S : FiniteSymbolicLatentSystem X ι) :
    _root_.Quotient (symbolicObservationalSetoid S) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) :=
  symbolicObservationQuotientRangeCompactHomeomorph S

noncomputable def symbolicObservationQuotientCompHaus
    (S : FiniteSymbolicLatentSystem X ι) : CompHaus := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (_root_.Quotient (symbolicObservationalSetoid S)) :=
    (quotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (_root_.Quotient (symbolicObservationalSetoid S)) :=
    (quotientRangeHomeomorph S).symm.t2Space
  exact CompHaus.of (_root_.Quotient (symbolicObservationalSetoid S))

noncomputable def symbolicObservationQuotientCompHausIso
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationQuotientCompHaus S ≅
      symbolicObservationRangeCompHaus S := by
  dsimp [symbolicObservationQuotientCompHaus,
    symbolicObservationRangeCompHaus]
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (_root_.Quotient (symbolicObservationalSetoid S)) :=
    (quotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (_root_.Quotient (symbolicObservationalSetoid S)) :=
    (quotientRangeHomeomorph S).symm.t2Space
  let e := quotientRangeHomeomorph S
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro q
        change e.symm (e q) = q
        exact e.symm_apply_apply q
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

@[simp] theorem symbolicObservationQuotientCompHausIso_hom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    (symbolicObservationQuotientCompHausIso S).hom q =
      symbolicObservationQuotientRangeMap S q :=
  rfl

theorem symbolicObservationQuotientCompHausIso_hom_forget
    (S : FiniteSymbolicLatentSystem X ι) :
    compHausToTop.map (symbolicObservationQuotientCompHausIso S).hom =
      symbolicObservationRangeCompHausTopCatHom S := by
  apply TopCat.hom_ext
  ext q
  rfl

noncomputable def symbolicObservationQuotientCompHausTopCatHom
    (S : FiniteSymbolicLatentSystem X ι) :
    compHausToTop.obj (symbolicObservationQuotientCompHaus S) ⟶
      compHausToTop.obj (symbolicObservationRangeCompHaus S) := by
  change TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
    TopCat.of (Set.range (symbolicObservationQuotientMap S))
  exact symbolicObservationQuotientRangeCompactTopCatHom S

theorem symbolicObservationQuotientCompHausTopCatHom_eq_hom_forget
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationQuotientCompHausTopCatHom S =
      compHausToTop.map (symbolicObservationQuotientCompHausIso S).hom := by
  apply TopCat.hom_ext
  ext q
  rfl

end InfoGeometry.Topology

end
