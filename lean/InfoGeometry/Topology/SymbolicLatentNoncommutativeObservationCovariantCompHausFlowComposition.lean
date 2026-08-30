import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausFlowIso

/-!
# Composition laws for covariant compact flow isomorphisms
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

theorem operatorCommutingLocusCovariantFlowIso_hom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) :
    (operatorCommutingLocusCovariantFlowIso Φ 0).hom =
      𝟙 (operatorCommutingLocusCompHaus S) := by
  rw [operatorCommutingLocusCovariantFlowIso_hom_eq_flowHom]
  exact operatorCommutingLocusCompHausCovariantFlowHom_zero Φ

theorem operatorCommutingLocusCovariantFlowIso_hom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (s t : ℝ) :
    (operatorCommutingLocusCovariantFlowIso Φ (s + t)).hom =
      (operatorCommutingLocusCovariantFlowIso Φ t).hom ≫
        (operatorCommutingLocusCovariantFlowIso Φ s).hom := by
  rw [operatorCommutingLocusCovariantFlowIso_hom_eq_flowHom,
    operatorCommutingLocusCovariantFlowIso_hom_eq_flowHom,
    operatorCommutingLocusCovariantFlowIso_hom_eq_flowHom]
  exact operatorCommutingLocusCompHausCovariantFlowHom_add Φ s t

theorem operatorCommutingLocusCovariantFlowIso_inv_eq_neg_hom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    (operatorCommutingLocusCovariantFlowIso Φ t).inv =
      (operatorCommutingLocusCovariantFlowIso Φ (-t)).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

end InfoGeometry.Topology
