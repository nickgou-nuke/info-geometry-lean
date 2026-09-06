import InfoGeometry.Topology.D4StarObservableEvaluation

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Observables on the quotient are determined by centre and outer values. -/

theorem continuousMap_ext_by_two_classes
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(D4StarQuotient, Y))
    (hcentre : f (starQuotientMap centralVertex) =
      g (starQuotientMap centralVertex))
    (houter : f (starQuotientMap (outerVertex ColorChannel.red)) =
      g (starQuotientMap (outerVertex ColorChannel.red))) :
    f = g := by
  ext q
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v with
      | inr u => exact hcentre
      | inl c =>
          change f (starQuotientMap (outerVertex c)) =
            g (starQuotientMap (outerVertex c))
          rw [outer_vertices_same_class c ColorChannel.red]
          exact houter

theorem quotientToBool_ext_by_two_classes
    (f g : D4StarQuotient → Bool)
    (hcentre : f (starQuotientMap centralVertex) =
      g (starQuotientMap centralVertex))
    (houter : f (starQuotientMap (outerVertex ColorChannel.red)) =
      g (starQuotientMap (outerVertex ColorChannel.red))) :
    f = g := by
  funext q
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v with
      | inr u => exact hcentre
      | inl c =>
          change f (starQuotientMap (outerVertex c)) =
            g (starQuotientMap (outerVertex c))
          rw [outer_vertices_same_class c ColorChannel.red]
          exact houter

end InfoGeometry.Topology.PauliJungD4Star
