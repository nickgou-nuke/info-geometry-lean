import InfoGeometry.Causal.ProofCarryingSchedule

namespace InfoGeometry.Causal.FiniteDependencySchedule

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]

theorem validSchedule_append (environment : Finset Node) (first second : List Node) :
    ValidSchedule environment (first ++ second) ↔
      ValidSchedule environment first ∧
      ValidSchedule (environment ∪ first.toFinset) second := by
  induction first generalizing environment with
  | nil => simp [ValidSchedule]
  | cons target remaining inductionHypothesis =>
    simp [ValidSchedule, inductionHypothesis, Finset.insert_union,
      Finset.union_insert, and_assoc]

theorem validSchedule_take_drop {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) (count : Nat) :
    ValidSchedule environment (schedule.take count) ∧
      ValidSchedule (environment ∪ (schedule.take count).toFinset) (schedule.drop count) := by
  apply (validSchedule_append environment (schedule.take count) (schedule.drop count)).mp
  simpa using valid

theorem validSchedule_prefix_closed {environment : Finset Node} {schedule : List Node}
    (closed : IsLowerSet (environment : Set Node))
    (valid : ValidSchedule environment schedule) (count : Nat) :
    IsLowerSet (↑(environment ∪ (schedule.take count).toFinset) : Set Node) :=
  validSchedule_isLowerSet closed (validSchedule_take_drop valid count).1

end InfoGeometry.Causal.FiniteDependencySchedule

namespace InfoGeometry.Causal.ProofCarryingSchedule

open FiniteDependencySchedule

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]
  {statement : Node → Prop}

omit [DecidableEq Node] in
theorem CertifiedState.ext_environment {first second : CertifiedState statement}
    (sameEnvironment : first.environment = second.environment) : first = second := by
  cases first
  cases second
  cases sameEnvironment
  rfl

def CertifiedState.execute (rules : ProofRules statement) (state : CertifiedState statement)
    (schedule : List Node) (valid : ValidSchedule state.environment schedule) :
    CertifiedState statement where
  environment := state.environment ∪ schedule.toFinset
  dependency_closed := validSchedule_isLowerSet state.dependency_closed valid
  proofs := validSchedule_preserves_proofs rules state.proofs valid

theorem CertifiedState.execute_append (rules : ProofRules statement)
    (state : CertifiedState statement) (first second : List Node)
    (firstValid : ValidSchedule state.environment first)
    (secondValid : ValidSchedule (state.environment ∪ first.toFinset) second) :
    state.execute rules (first ++ second)
        ((validSchedule_append _ _ _).mpr ⟨firstValid, secondValid⟩) =
      (state.execute rules first firstValid).execute rules second secondValid := by
  apply CertifiedState.ext_environment
  simp [CertifiedState.execute, Finset.union_assoc]

theorem CertifiedState.execute_eq_of_perm (rules : ProofRules statement)
    (state : CertifiedState statement) {first second : List Node}
    (firstValid : ValidSchedule state.environment first)
    (secondValid : ValidSchedule state.environment second) (permutation : first.Perm second) :
    state.execute rules first firstValid = state.execute rules second secondValid := by
  apply CertifiedState.ext_environment
  change state.environment ∪ first.toFinset = state.environment ∪ second.toFinset
  rw [List.toFinset_eq_of_perm _ _ permutation]

theorem CertifiedState.execute_prefix_proofs (rules : ProofRules statement)
    (state : CertifiedState statement) {schedule : List Node}
    (valid : ValidSchedule state.environment schedule) (count : Nat) :
    HasProofs statement (state.environment ∪ (schedule.take count).toFinset) :=
  validSchedule_preserves_proofs rules state.proofs (validSchedule_take_drop valid count).1

end InfoGeometry.Causal.ProofCarryingSchedule
