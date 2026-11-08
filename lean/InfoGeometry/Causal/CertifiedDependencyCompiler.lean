import InfoGeometry.Causal.FiniteDependencyCompiler
import InfoGeometry.Causal.DependencyScheduleComposition

namespace InfoGeometry.Causal.CertifiedDependencyCompiler

open FiniteDependencySchedule FiniteDependencyCompiler ProofCarryingSchedule

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]
  [Fintype Node] [DecidableLT Node] {statement : Node → Prop}

def compileCertified (rules : ProofRules statement) (state : CertifiedState statement)
    (pending : List Node) : Option (CertifiedState statement) :=
  match computed : compile state.environment pending with
  | none => none
  | some schedule => some (state.execute rules schedule (compile_sound computed).1)

theorem compileCertified_eq_some {rules : ProofRules statement}
    {state : CertifiedState statement} {pending schedule : List Node}
    (computed : compile state.environment pending = some schedule) :
    compileCertified rules state pending =
      some (state.execute rules schedule (compile_sound computed).1) := by
  unfold compileCertified
  split
  next absent =>
    rw [computed] at absent
    cases absent
  next output success =>
    have equal : output = schedule := Option.some.inj (success.symm.trans computed)
    subst output
    rfl

theorem compileCertified_eq_none {rules : ProofRules statement}
    {state : CertifiedState statement} {pending : List Node}
    (computed : compile state.environment pending = none) :
    compileCertified rules state pending = none := by
  unfold compileCertified
  split
  · rfl
  next schedule success =>
    rw [computed] at success
    cases success

theorem compileCertified_sound {rules : ProofRules statement}
    {state completed : CertifiedState statement} {pending : List Node}
    (computed : compileCertified rules state pending = some completed) :
    ∃ schedule, compile state.environment pending = some schedule ∧
      ValidSchedule state.environment schedule ∧ schedule.Perm pending ∧
      completed.environment = state.environment ∪ pending.toFinset := by
  cases scheduled : compile state.environment pending with
  | none =>
    rw [compileCertified_eq_none scheduled] at computed
    cases computed
  | some schedule =>
    rw [compileCertified_eq_some scheduled] at computed
    cases Option.some.inj computed
    obtain ⟨valid, permutation⟩ := compile_sound scheduled
    refine ⟨schedule, rfl, valid, permutation, ?_⟩
    change state.environment ∪ schedule.toFinset = state.environment ∪ pending.toFinset
    rw [List.toFinset_eq_of_perm _ _ permutation]

theorem compileCertified_complete (rules : ProofRules statement)
    (state : CertifiedState statement) (targetSet : Finset Node) (pending : List Node)
    (inclusion : state.environment ⊆ targetSet)
    (closed : IsLowerSet (targetSet : Set Node)) (distinct : pending.Nodup)
    (coverage : pending.toFinset = targetSet \ state.environment) :
    ∃ completed, compileCertified rules state pending = some completed ∧
      completed.environment = targetSet := by
  obtain ⟨schedule, computed, valid, permutation⟩ :=
    compile_complete state.environment targetSet pending closed distinct coverage
  refine ⟨state.execute rules schedule valid, compileCertified_eq_some computed, ?_⟩
  change state.environment ∪ schedule.toFinset = targetSet
  rw [List.toFinset_eq_of_perm _ _ permutation, coverage]
  ext node
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (present | ⟨present, _⟩)
    · exact inclusion present
    · exact present
  · intro present
    by_cases previous : node ∈ state.environment
    · exact Or.inl previous
    · exact Or.inr ⟨present, previous⟩

theorem compileCertified_proves_target (rules : ProofRules statement)
    (state : CertifiedState statement) (targetSet : Finset Node) (pending : List Node)
    (inclusion : state.environment ⊆ targetSet)
    (closed : IsLowerSet (targetSet : Set Node)) (distinct : pending.Nodup)
    (coverage : pending.toFinset = targetSet \ state.environment) :
    ∃ completed, compileCertified rules state pending = some completed ∧
      completed.environment = targetSet ∧ HasProofs statement targetSet := by
  obtain ⟨completed, computed, complete⟩ := compileCertified_complete
    rules state targetSet pending inclusion closed distinct coverage
  exact ⟨completed, computed, complete, complete ▸ completed.proofs⟩

end InfoGeometry.Causal.CertifiedDependencyCompiler
