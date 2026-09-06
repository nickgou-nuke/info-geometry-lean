import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus

/-!
# Bijective boundary-cylinder readout in `CompHaus`

Under the explicit injectivity and surjectivity hypotheses already used by the
`TopCat` owner, the compact-Hausdorff readout is an isomorphism as well.  The
proof uses the fully faithful forgetful functor rather than constructing a
second inverse map.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat

variable {ι : Type} {A : Type}
  [Fintype ι] [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [T2Space A]
variable {D : SymbolicLatentSequence ι}

theorem boundaryReadoutCompHausHom_isIso_of_bijective
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    IsIso (boundaryReadoutCompHausHom S) := by
  have hIso : IsIso (compHausToTop.map (boundaryReadoutCompHausHom S)) := by
    rw [boundaryReadoutCompHausHom_forget S]
    exact boundaryReadout_isIso_of_bijective S h_inj h_surj
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  exact hFF.isIso_of_isIso_map (boundaryReadoutCompHausHom S)

noncomputable def boundaryReadoutCompHausIso
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    CompHaus.of ((colimit (carrierDiagram D) : TopCat) : Type) ≅
      CompHaus.of (ℕ → A) := by
  letI : IsIso (boundaryReadoutCompHausHom S) :=
    boundaryReadoutCompHausHom_isIso_of_bijective S h_inj h_surj
  exact asIso (boundaryReadoutCompHausHom S)

@[simp] theorem boundaryReadoutCompHausIso_hom_forget
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    compHausToTop.map (boundaryReadoutCompHausIso S h_inj h_surj).hom =
      boundaryReadout D S := by
  rfl

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus

end
