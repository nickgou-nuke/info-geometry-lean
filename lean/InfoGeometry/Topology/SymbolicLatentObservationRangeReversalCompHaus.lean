import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompHausFunctor
import InfoGeometry.Topology.SymbolicLatentObservationQuotientReversalCompHaus

/-!
# Reversal and flow transported to observation ranges

The quotient-side actions are transported through the existing natural
isomorphism between observational quotients and their compact observation
ranges.  This owner therefore introduces no second range action and no new
readout covariance axiom.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

noncomputable def SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
    symbolicObservationRangeCompHaus S ⟶
      symbolicObservationRangeCompHaus S :=
  (symbolicObservationQuotientCompHausIso S).inv ≫
    R.toQuotientCompHausHom h_cont ≫
      (symbolicObservationQuotientCompHausIso S).hom

noncomputable def SymbolicLatentObservableModularFlow.toObservationRangeCompHausHom
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    symbolicObservationRangeCompHaus S ⟶
      symbolicObservationRangeCompHaus S :=
  (symbolicObservationQuotientCompHausIso S).inv ≫
    Φ.toQuotientCompHausHom h_flow t ≫
      (symbolicObservationQuotientCompHausIso S).hom

theorem SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom_square
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R)) :
      R.toObservationRangeCompHausHom h_cont ≫
        R.toObservationRangeCompHausHom h_cont =
      𝟙 (symbolicObservationRangeCompHaus S) := by
  simp only [SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    (R.toQuotientCompHausHom h_cont)
    (R.toQuotientCompHausHom h_cont)
    (symbolicObservationQuotientCompHausIso S).hom]
  rw [R.toQuotientCompHausHom_square h_cont]
  simp

theorem SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom_flow_reversal
    {S : FiniteSymbolicLatentSystem X ι}
    {Φ : SymbolicLatentObservableModularFlow S}
    (R : SymbolicLatentObservableModularReversal Φ)
    (h_flow : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (h_cont : Continuous (descendedSymbolicLatentObservationInvolution R))
    (t : ℝ) :
    Φ.toObservationRangeCompHausHom h_flow t ≫
        R.toObservationRangeCompHausHom h_cont =
      R.toObservationRangeCompHausHom h_cont ≫
        Φ.toObservationRangeCompHausHom h_flow (-t) := by
  simp only [SymbolicLatentObservableModularFlow.toObservationRangeCompHausHom,
    SymbolicLatentObservableModularReversal.toObservationRangeCompHausHom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    (Φ.toQuotientCompHausHom h_flow t)
    (R.toQuotientCompHausHom h_cont)
    (symbolicObservationQuotientCompHausIso S).hom]
  rw [← Category.assoc
    (R.toQuotientCompHausHom h_cont)
    (Φ.toQuotientCompHausHom h_flow (-t))
    (symbolicObservationQuotientCompHausIso S).hom]
  rw [R.toQuotientCompHausHom_flow_reversal h_flow h_cont t]

end InfoGeometry.Topology

end
