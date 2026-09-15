import InfoGeometry.Causal.MetaCompiler

namespace InfoGeometry.Causal.MetaCompiler.Tests

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule

example {Node : Type*} [PartialOrder Node] [DecidableEq Node] [Fintype Node]
    (statement : Node → Prop) (rules : ProofRules statement) :
    ∃ schedule : List Node,
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, statement target :=
  InfoGeometry.MetaCompiler.finite_certified_compilation statement rules

example {α : Type*} [PartialOrder α] (a b : α)
    (hab : a < b) (hba : b < a) : False :=
  no_circular_hallucination a b hab hba

example {Node : Type*} [PartialOrder Node] [DecidableEq Node]
    (nodes : Finset Node) (nonempty : nodes.Nonempty) :
    ∃ minimal ∈ nodes, ∀ candidate ∈ nodes, ¬ candidate < minimal :=
  exists_minimal_element nodes nonempty

example {Node : Type*} [PartialOrder Node] [DecidableEq Node]
    (nodes : Finset Node) :
    (topologicalSort nodes).toFinset = nodes :=
  (topologicalSort_spec nodes).2.2.1

example : topologicalSort (∅ : Finset (Fin 0)) = [] := by
  simp [topologicalSort]

example [PartialOrder (Fin 3)] :
    (topologicalSort (Finset.univ : Finset (Fin 3))).length = 3 := by
  simpa using (topologicalSort_spec (Finset.univ : Finset (Fin 3))).2.1

end InfoGeometry.Causal.MetaCompiler.Tests
