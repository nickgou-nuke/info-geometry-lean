import InfoGeometry.Topology.D4StarQuotientClopen

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! The two clopen classes form a genuine partition of the quotient. -/

theorem centreClass_union_outerClass :
    centreClass ∪ outerClass = (Set.univ : Set D4StarQuotient) := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v with
      | inr u =>
          cases u
          change starQuotientMap centralVertex ∈ centreClass ∪ outerClass
          change (starQuotientMap centralVertex =
              starQuotientMap centralVertex ∨
              starQuotientMap centralVertex =
                starQuotientMap (outerVertex ColorChannel.red))
          exact Or.inl rfl
      | inl c =>
          change starQuotientMap (outerVertex c) ∈ centreClass ∪ outerClass
          change (starQuotientMap (outerVertex c) =
              starQuotientMap centralVertex ∨
              starQuotientMap (outerVertex c) =
                starQuotientMap (outerVertex ColorChannel.red))
          exact Or.inr (outer_vertices_same_class c ColorChannel.red)

theorem centreClass_inter_outerClass :
    centreClass ∩ outerClass = (∅ : Set D4StarQuotient) := by
  ext q
  constructor
  · intro hq
    exact False.elim (centreClass_disjoint_outerClass.le_bot ⟨hq.1, hq.2⟩)
  · intro hq
    exact False.elim hq

theorem centreClass_partition_outerClass :
    Disjoint centreClass outerClass ∧
      centreClass ∪ outerClass = (Set.univ : Set D4StarQuotient) :=
  ⟨centreClass_disjoint_outerClass, centreClass_union_outerClass⟩

end InfoGeometry.Topology.PauliJungD4Star
