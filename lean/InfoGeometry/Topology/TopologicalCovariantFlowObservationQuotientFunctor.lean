import InfoGeometry.Topology.TopologicalCovariantFlowObservationRangeFunctor
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quotient observation functor and its range comparison

The noncommutative observation quotient is already known to be compact
Hausdorff and canonically isomorphic to the operator-valued observation range.
This owner makes that objectwise fact functorial for the fixed-carrier
topological covariant-flow category.  The quotient action is defined by
conjugating the range action through the canonical `CompHaus` isomorphism;
continuity is therefore inherited rather than postulated.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

variable {S : NoncommutativeObservableSystem X A ι}

noncomputable def operatorObservationQuotientCompHausHomOfMorphism
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    operatorObservationQuotientCompHaus S ⟶
      operatorObservationQuotientCompHaus S :=
  (operatorObservationQuotientCompHausIso S).hom ≫
    operatorObservationRangeCompHausHomOfMorphism f ≫
    (operatorObservationQuotientCompHausIso S).inv

@[simp] theorem operatorObservationQuotientCompHausHomOfMorphism_apply
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (q : OperatorObservationalQuotient S) :
    operatorObservationQuotientCompHausHomOfMorphism f q =
      (operatorObservationQuotientCompHausIso S).inv
        (operatorObservationRangeCompHausHomOfMorphism f
          ((operatorObservationQuotientCompHausIso S).hom q)) := by
  rfl

noncomputable def operatorObservationQuotientCompHausFunctor :
    NoncommutativeObservableTopologicalCovariantFlow S ⥤ CompHaus where
  obj _ := operatorObservationQuotientCompHaus S
  map f := operatorObservationQuotientCompHausHomOfMorphism f
  map_id := by
    intro F
    change (operatorObservationQuotientCompHausIso S).hom ≫
        (operatorObservationRangeCompHausFunctor (S := S)).map (𝟙 F) ≫
        (operatorObservationQuotientCompHausIso S).inv = 𝟙 _
    rw [(operatorObservationRangeCompHausFunctor (S := S)).map_id F]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      (operatorObservationQuotientCompHausIso S).hom_inv_id
  map_comp f g := by
    change (operatorObservationQuotientCompHausIso S).hom ≫
        (operatorObservationRangeCompHausFunctor (S := S)).map (f ≫ g) ≫
        (operatorObservationQuotientCompHausIso S).inv =
      ((operatorObservationQuotientCompHausIso S).hom ≫
        (operatorObservationRangeCompHausFunctor (S := S)).map f ≫
        (operatorObservationQuotientCompHausIso S).inv) ≫
      ((operatorObservationQuotientCompHausIso S).hom ≫
        (operatorObservationRangeCompHausFunctor (S := S)).map g ≫
        (operatorObservationQuotientCompHausIso S).inv)
    rw [(operatorObservationRangeCompHausFunctor (S := S)).map_comp f g]
    simp [Category.assoc]

noncomputable def operatorObservationQuotientRangeCompHausIso :
    operatorObservationQuotientCompHausFunctor (S := S) ≅
      operatorObservationRangeCompHausFunctor (S := S) := by
  refine NatIso.ofComponents
    (fun _ => operatorObservationQuotientCompHausIso S) ?_
  intro F G f
  change ((operatorObservationQuotientCompHausIso S).hom ≫
      (operatorObservationRangeCompHausFunctor (S := S)).map f ≫
      (operatorObservationQuotientCompHausIso S).inv) ≫
      (operatorObservationQuotientCompHausIso S).hom =
    (operatorObservationQuotientCompHausIso S).hom ≫
      (operatorObservationRangeCompHausFunctor (S := S)).map f
  simp [Category.assoc]

theorem operatorObservationQuotientRangeCompHausIso_naturality_apply
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (q : OperatorObservationalQuotient S) :
    ((operatorObservationQuotientCompHausFunctor (S := S)).map f ≫
        (operatorObservationQuotientRangeCompHausIso (S := S)).hom.app G) q =
      ((operatorObservationQuotientRangeCompHausIso (S := S)).hom.app F ≫
        (operatorObservationRangeCompHausFunctor (S := S)).map f) q := by
  exact congrArg (fun h => h q)
    ((operatorObservationQuotientRangeCompHausIso (S := S)).hom.naturality f)

end InfoGeometry.Topology
