import Lean.Data.Name
import InfoGeometry.Causal.CertifiedDependencyCompiler

namespace InfoGeometry.MetaCompiler.DeclarationBridge

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]

/-- A supplied dependency relation with explicit coverage and ordering witnesses.
This structure does not certify extraction from a Lean environment. -/
structure DependencyCorrespondence (Node : Type*) [PartialOrder Node] where
  declaration : Node ↪ Lean.Name
  depends : Lean.Name → Lean.Name → Prop
  resolve :
    ∀ target prerequisite, depends prerequisite (declaration target) →
      ∃ source, declaration source = prerequisite ∧ source < target

def DependencyCorrespondence.Closed
    (bridge : DependencyCorrespondence Node) (environment : Finset Node) : Prop :=
  ∀ target ∈ environment,
    ∀ prerequisite, bridge.depends prerequisite (bridge.declaration target) →
      ∃ source ∈ environment, bridge.declaration source = prerequisite

theorem DependencyCorrespondence.dependency_precedes
    (bridge : DependencyCorrespondence Node) {source target : Node}
    (dependency : bridge.depends
      (bridge.declaration source) (bridge.declaration target)) :
    source < target := by
  obtain ⟨resolved, sameName, precedes⟩ :=
    bridge.resolve target (bridge.declaration source) dependency
  have sameNode : resolved = source := bridge.declaration.injective sameName
  subst resolved
  exact precedes

theorem DependencyCorrespondence.not_depends_self
    (bridge : DependencyCorrespondence Node) (target : Node) :
    ¬ bridge.depends (bridge.declaration target) (bridge.declaration target) := by
  intro dependency
  exact lt_irrefl target (bridge.dependency_precedes dependency)

theorem DependencyCorrespondence.closed_of_isLowerSet
    (bridge : DependencyCorrespondence Node) {environment : Finset Node}
    (closed : IsLowerSet (environment : Set Node)) :
    bridge.Closed environment := by
  intro target membership prerequisite dependency
  obtain ⟨source, sameName, precedes⟩ :=
    bridge.resolve target prerequisite dependency
  exact ⟨source, closed precedes.le membership, sameName⟩

theorem DependencyCorrespondence.schedule_respects_dependencies
    (bridge : DependencyCorrespondence Node)
    {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) :
    schedule.Pairwise (fun earlier later =>
      ¬ bridge.depends
        (bridge.declaration later) (bridge.declaration earlier)) := by
  apply (validSchedule_pairwise valid).imp
  intro earlier later ordered dependency
  exact ordered (bridge.dependency_precedes dependency).le

theorem DependencyCorrespondence.prefix_closed
    (bridge : DependencyCorrespondence Node)
    {environment : Finset Node} {schedule : List Node}
    (closed : IsLowerSet (environment : Set Node))
    (valid : ValidSchedule environment schedule) (count : Nat) :
    bridge.Closed (environment ∪ (schedule.take count).toFinset) := by
  exact bridge.closed_of_isLowerSet
    (validSchedule_prefix_closed closed valid count)

theorem DependencyCorrespondence.prefix_has_dependency_proofs
    (bridge : DependencyCorrespondence Node)
    {statement : Node → Prop}
    (rules : ProofRules statement) (state : CertifiedState statement)
    {schedule : List Node}
    (valid : ValidSchedule state.environment schedule) (count : Nat) :
    ∀ target ∈ state.environment ∪ (schedule.take count).toFinset,
      ∀ prerequisite, bridge.depends prerequisite (bridge.declaration target) →
        ∃ source,
          source ∈ state.environment ∪ (schedule.take count).toFinset ∧
          bridge.declaration source = prerequisite ∧ statement source := by
  intro target membership prerequisite dependency
  obtain ⟨source, present, sameName⟩ :=
    bridge.prefix_closed state.dependency_closed valid count
      target membership prerequisite dependency
  exact ⟨source, present, sameName,
    state.execute_prefix_proofs rules valid count source present⟩

variable [Fintype Node] [DecidableLT Node]

theorem certified_compilation_preserves_named_dependencies
    (bridge : DependencyCorrespondence Node)
    {statement : Node → Prop}
    (rules : ProofRules statement)
    (state completed : CertifiedState statement)
    (pending : List Node)
    (computed : compileCertified rules state pending = some completed) :
    ∃ schedule,
      compile state.environment pending = some schedule ∧
      schedule.Perm pending ∧
      schedule.Pairwise (fun earlier later =>
        ¬ bridge.depends
          (bridge.declaration later) (bridge.declaration earlier)) ∧
      completed.environment = state.environment ∪ pending.toFinset ∧
      bridge.Closed completed.environment ∧
      HasProofs statement completed.environment ∧
      ∀ count,
        bridge.Closed (state.environment ∪ (schedule.take count).toFinset) ∧
        HasProofs statement
          (state.environment ∪ (schedule.take count).toFinset) := by
  obtain ⟨schedule, scheduled, valid, permutation, coverage⟩ :=
    compileCertified_sound computed
  refine ⟨schedule, scheduled, permutation,
    bridge.schedule_respects_dependencies valid, coverage,
    bridge.closed_of_isLowerSet completed.dependency_closed,
    completed.proofs, ?_⟩
  intro count
  exact ⟨bridge.prefix_closed state.dependency_closed valid count,
    state.execute_prefix_proofs rules valid count⟩

end InfoGeometry.MetaCompiler.DeclarationBridge
