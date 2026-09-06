import InfoGeometry.Topology.TopologicalCovariantFlowObservationQuotientFunctor
import InfoGeometry.Topology.TopologicalCovariantFlowCompHausFunctor

/-!
# Topological quotient flow laws

The quotient-side time action for a topological covariant flow is obtained by
conjugating the already established range-side `CompHaus` isomorphism through
the canonical quotient/range isomorphism.  The group laws are consequently
transported, not reproved from a second quotient construction.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def topologicalCovariantQuotientCompHausIso
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ) :
    operatorObservationQuotientCompHaus S ≅
      operatorObservationQuotientCompHaus S :=
  (operatorObservationQuotientCompHausIso S).trans
    ((topologicalCovariantRangeCompHausIso F t).trans
      (operatorObservationQuotientCompHausIso S).symm)

@[simp] theorem topologicalCovariantQuotientCompHausIso_hom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ)
    (q : operatorObservationQuotientCompHaus S) :
    (topologicalCovariantQuotientCompHausIso F t).hom q =
      (operatorObservationQuotientCompHausIso S).inv
        ((topologicalCovariantRangeCompHausIso F t).hom
          ((operatorObservationQuotientCompHausIso S).hom q)) := by
  rfl

theorem topologicalCovariantQuotientCompHausIso_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (topologicalCovariantQuotientCompHausIso F 0).hom =
      𝟙 (operatorObservationQuotientCompHaus S) := by
  change (operatorObservationQuotientCompHausIso S).hom ≫
      (topologicalCovariantRangeCompHausIso F 0).hom ≫
      (operatorObservationQuotientCompHausIso S).inv = 𝟙 _
  rw [topologicalCovariantRangeCompHausIso_zero]
  simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
    (operatorObservationQuotientCompHausIso S).hom_inv_id

theorem topologicalCovariantQuotientCompHausIso_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (s t : ℝ) :
    (topologicalCovariantQuotientCompHausIso F (s + t)).hom =
      (topologicalCovariantQuotientCompHausIso F t).hom ≫
        (topologicalCovariantQuotientCompHausIso F s).hom := by
  change (operatorObservationQuotientCompHausIso S).hom ≫
      (topologicalCovariantRangeCompHausIso F (s + t)).hom ≫
      (operatorObservationQuotientCompHausIso S).inv =
    ((operatorObservationQuotientCompHausIso S).hom ≫
      (topologicalCovariantRangeCompHausIso F t).hom ≫
      (operatorObservationQuotientCompHausIso S).inv) ≫
    ((operatorObservationQuotientCompHausIso S).hom ≫
      (topologicalCovariantRangeCompHausIso F s).hom ≫
      (operatorObservationQuotientCompHausIso S).inv)
  rw [topologicalCovariantRangeCompHausIso_add]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem topologicalCovariantQuotientCompHausIso_inv_eq_neg_hom
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ) :
    (topologicalCovariantQuotientCompHausIso F t).inv =
      (topologicalCovariantQuotientCompHausIso F (-t)).hom := by
  change (operatorObservationQuotientCompHausIso S).hom ≫
      (topologicalCovariantRangeCompHausIso F t).inv ≫
      (operatorObservationQuotientCompHausIso S).inv =
    (operatorObservationQuotientCompHausIso S).hom ≫
      (topologicalCovariantRangeCompHausIso F (-t)).hom ≫
      (operatorObservationQuotientCompHausIso S).inv
  rw [topologicalCovariantRangeCompHausIso_inv_eq_neg_hom]

end InfoGeometry.Topology

