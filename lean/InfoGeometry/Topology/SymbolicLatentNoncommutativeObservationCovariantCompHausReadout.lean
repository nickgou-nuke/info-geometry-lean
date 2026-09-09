import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantQuotientCompHausFlow

/-!
# Covariant readout of compact operator-valued quotients

The compact readout is the canonical quotient-to-range `CompHaus` morphism.
Covariance is stated on the underlying operator-valued readout.  No
continuity of an arbitrary `StarAlgEquiv` is assumed or invented here.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorObservationQuotientCompHausReadoutHom
    (S : NoncommutativeObservableSystem X A ι) :
    operatorObservationQuotientCompHaus S ⟶
      operatorObservationRangeCompHaus S :=
  (operatorObservationQuotientCompHausIso S).hom

@[simp] theorem operatorObservationQuotientCompHausReadoutHom_apply
    (S : NoncommutativeObservableSystem X A ι)
    (q : OperatorObservationalQuotient S) :
    operatorObservationQuotientCompHausReadoutHom S q =
      operatorObservationQuotientRangeMap S q := by
  rfl

theorem operatorObservationQuotientCompHausReadoutHom_forget
    (S : NoncommutativeObservableSystem X A ι) :
    compHausToTop.map (operatorObservationQuotientCompHausReadoutHom S) =
      TopCat.ofHom
        { toFun := operatorObservationQuotientRangeMap S
          continuous_toFun := continuous_operatorObservationQuotientRangeMap S } := by
  apply TopCat.hom_ext
  ext q
  rfl

theorem operatorObservationQuotientCompHausReadout_covariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (q : OperatorObservationalQuotient S) :
    (operatorObservationQuotientCompHausReadoutHom S
        (operatorObservationQuotientCompHausCovariantFlowHom Φ t q)).1 =
      fun i => Φ.operatorAction t
        ((operatorObservationQuotientCompHausReadoutHom S q).1 i) := by
  change (operatorObservationQuotientRangeMap S
      (descendedCovariantOperatorObservationFlow Φ t q)).1 =
    fun i => Φ.operatorAction t
      ((operatorObservationQuotientRangeMap S q).1 i)
  rw [operatorObservationQuotientRangeMap_val,
    operatorObservationQuotientRangeMap_val]
  exact operatorObservationQuotientReadout_covariant Φ t q

end InfoGeometry.Topology
