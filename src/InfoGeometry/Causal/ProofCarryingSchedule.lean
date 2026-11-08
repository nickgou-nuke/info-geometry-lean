import InfoGeometry.Causal.FiniteDependencySchedule

namespace InfoGeometry.Causal.ProofCarryingSchedule

open FiniteDependencySchedule

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]

def HasProofs (statement : Node → Prop) (environment : Finset Node) : Prop :=
  ∀ target ∈ environment, statement target

def ProofRules (statement : Node → Prop) : Prop :=
  ∀ target, (∀ prerequisite, prerequisite < target → statement prerequisite) → statement target

structure CertifiedState (statement : Node → Prop) where
  environment : Finset Node
  dependency_closed : IsLowerSet (environment : Set Node)
  proofs : HasProofs statement environment

omit [DecidableEq Node] in
theorem proof_of_admissible {statement : Node → Prop} {environment : Finset Node}
    {target : Node} (rules : ProofRules statement) (evidence : HasProofs statement environment)
    (admissible : IsAdmissible environment target) : statement target :=
  rules target (fun prerequisite precedes =>
    evidence prerequisite (admissible prerequisite precedes))

omit [PartialOrder Node] in
theorem hasProofs_insert {statement : Node → Prop} {environment : Finset Node}
    {target : Node} (evidence : HasProofs statement environment) (proof : statement target) :
    HasProofs statement (insert target environment) := by
  intro node membership
  rcases Finset.mem_insert.mp membership with rfl | membership
  · exact proof
  · exact evidence node membership

def CertifiedState.extend {statement : Node → Prop} (state : CertifiedState statement)
    (target : Node) (ready : IsReady state.environment target) (proof : statement target) :
    CertifiedState statement where
  environment := insert target state.environment
  dependency_closed := insert_isLowerSet state.dependency_closed ready.2
  proofs := hasProofs_insert state.proofs proof

theorem validSchedule_preserves_proofs {statement : Node → Prop}
    {environment : Finset Node} {schedule : List Node}
    (rules : ProofRules statement) (evidence : HasProofs statement environment)
    (valid : ValidSchedule environment schedule) :
    HasProofs statement (environment ∪ schedule.toFinset) := by
  induction schedule generalizing environment with
  | nil => simpa using evidence
  | cons first remaining inductionHypothesis =>
    have extended := hasProofs_insert evidence (proof_of_admissible rules evidence valid.1.2)
    simpa [Finset.insert_union, Finset.union_insert] using
      inductionHypothesis extended valid.2

theorem finite_proof_compilation [Fintype Node] (statement : Node → Prop)
    (rules : ProofRules statement) :
    ∃ schedule : List Node, ValidSchedule ∅ schedule ∧ schedule.Nodup ∧
      schedule.toFinset = Finset.univ ∧ ∀ target, statement target := by
  obtain ⟨schedule, valid, distinct, complete⟩ := exists_topological_schedule (Node := Node)
  have evidence : HasProofs statement ∅ := by
    intro target membership
    exact False.elim (Finset.notMem_empty _ membership)
  have compiled := validSchedule_preserves_proofs rules evidence valid
  refine ⟨schedule, valid, distinct, complete, ?_⟩
  intro target
  apply compiled target
  simp [complete]

end InfoGeometry.Causal.ProofCarryingSchedule
