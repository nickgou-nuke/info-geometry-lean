import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCompHausFlowIso

/-!
# Composition laws for compact operator-commuting flow isomorphisms

This owner packages the categorical time-slice laws from the existing
`CompHaus` flow morphisms.  The order is inherited from the native flow
convention and is not rederived by an independent action law.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [Fintype ι]

theorem operatorCommutingLocusCompHausFlowIso_hom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) :
    (operatorCommutingLocusCompHausFlowIso Φ 0).hom =
      𝟙 (operatorCommutingLocusCompHaus S) := by
  rw [operatorCommutingLocusCompHausFlowIso_hom_eq_flowHom]
  exact operatorCommutingLocusCompHausFlowHom_zero Φ

theorem operatorCommutingLocusCompHausFlowIso_hom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (s t : ℝ) :
    (operatorCommutingLocusCompHausFlowIso Φ (s + t)).hom =
      (operatorCommutingLocusCompHausFlowIso Φ s).hom ≫
        (operatorCommutingLocusCompHausFlowIso Φ t).hom := by
  rw [operatorCommutingLocusCompHausFlowIso_hom_eq_flowHom,
    operatorCommutingLocusCompHausFlowIso_hom_eq_flowHom,
    operatorCommutingLocusCompHausFlowIso_hom_eq_flowHom]
  exact operatorCommutingLocusCompHausFlowHom_add Φ s t

theorem operatorCommutingLocusCompHausFlowIso_inv_eq_neg_hom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) :
    (operatorCommutingLocusCompHausFlowIso Φ t).inv =
      (operatorCommutingLocusCompHausFlowIso Φ (-t)).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

end InfoGeometry.Topology
