import InfoGeometry.Topology.TopologicalCovariantFlowObservationQuotientFlowLaws

/-!
# Additive flows of compact-Hausdorff isomorphisms

This is the small categorical carrier for a real-time flow on one compact
Hausdorff object.  It deliberately stores `CategoryTheory.Iso` values rather
than assuming an ambient topological group or an analytic exponential.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

structure CompHausAdditiveIsoFlow (Y : CompHaus) where
  act : ℝ → (Y ≅ Y)
  zero : (act 0).hom = 𝟙 Y
  add : ∀ s t, (act (s + t)).hom = (act t).hom ≫ (act s).hom
  neg : ∀ t, (act t).inv = (act (-t)).hom

theorem CompHausAdditiveIsoFlow.hom_zero
    {Y : CompHaus} (F : CompHausAdditiveIsoFlow Y) :
    (F.act 0).hom = 𝟙 Y := by
  exact F.zero

theorem CompHausAdditiveIsoFlow.hom_add
    {Y : CompHaus} (F : CompHausAdditiveIsoFlow Y) (s t : ℝ) :
    (F.act (s + t)).hom = (F.act t).hom ≫ (F.act s).hom := by
  exact F.add s t

theorem CompHausAdditiveIsoFlow.hom_inv_eq_neg_hom
    {Y : CompHaus} (F : CompHausAdditiveIsoFlow Y) (t : ℝ) :
    (F.act t).inv = (F.act (-t)).hom :=
  F.neg t

noncomputable def topologicalCovariantQuotientCompHausIsoFlow
    {X A ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    CompHausAdditiveIsoFlow (operatorObservationQuotientCompHaus S) where
  act := topologicalCovariantQuotientCompHausIso F
  zero := topologicalCovariantQuotientCompHausIso_zero F
  add := topologicalCovariantQuotientCompHausIso_add F
  neg := topologicalCovariantQuotientCompHausIso_inv_eq_neg_hom F

theorem topologicalCovariantQuotientCompHausIsoFlow_hom_zero
    {X A ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    ((topologicalCovariantQuotientCompHausIsoFlow F).act 0).hom =
      𝟙 (operatorObservationQuotientCompHaus S) :=
  (topologicalCovariantQuotientCompHausIsoFlow F).hom_zero

theorem topologicalCovariantQuotientCompHausIsoFlow_hom_add
    {X A ι : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (s t : ℝ) :
    ((topologicalCovariantQuotientCompHausIsoFlow F).act (s + t)).hom =
      ((topologicalCovariantQuotientCompHausIsoFlow F).act t).hom ≫
        ((topologicalCovariantQuotientCompHausIsoFlow F).act s).hom :=
  (topologicalCovariantQuotientCompHausIsoFlow F).hom_add s t

end InfoGeometry.Topology
