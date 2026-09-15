import InfoGeometry.Causal.CertifiedDependencyCompiler
import InfoGeometry.Causal.VerifiedDevelopmentState
import InfoGeometry.Meta.DeclaredResearchDependencies

namespace InfoGeometry.MetaCompiler

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule

namespace DeclaredProtocol

inductive Archetype
  | statementSpecification
  | dependencyOrder
  | admissibility
  | topologicalSchedule
  | proofEvidence
  | certifiedCompilation
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | statementSpecification => {statementSpecification}
  | dependencyOrder => {statementSpecification, dependencyOrder}
  | admissibility => {statementSpecification, dependencyOrder, admissibility}
  | topologicalSchedule =>
      {statementSpecification, dependencyOrder, admissibility, topologicalSchedule}
  | proofEvidence => {statementSpecification, proofEvidence}
  | certifiedCompilation =>
      {statementSpecification, dependencyOrder, admissibility, topologicalSchedule,
        proofEvidence, certifiedCompilation}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

instance : DecidableLT Archetype := fun earlier later =>
  decidable_of_iff (earlier ≤ later ∧ ¬ later ≤ earlier) lt_iff_le_not_ge.symm

theorem prerequisite_iff_le (earlier later : Archetype) :
    earlier ∈ prerequisites later ↔ earlier ≤ later := by
  cases earlier <;> cases later <;> decide

theorem admissible_iff_prerequisites (environment : Finset Archetype) (target : Archetype) :
    IsAdmissible environment target ↔ (prerequisites target).erase target ⊆ environment := by
  constructor
  · intro admissible earlier membership
    rcases Finset.mem_erase.mp membership with ⟨distinct, ancestor⟩
    exact admissible earlier (lt_of_le_of_ne ((prerequisite_iff_le _ _).mp ancestor) distinct)
  · intro included earlier precedes
    exact included (Finset.mem_erase.mpr
      ⟨ne_of_lt precedes, (prerequisite_iff_le _ _).mpr precedes.le⟩)

theorem scheduling_and_evidence_incomparable :
    ¬ topologicalSchedule ≤ proofEvidence ∧ ¬ proofEvidence ≤ topologicalSchedule := by
  decide

theorem specification_admissible_empty : IsReady ∅ statementSpecification := by
  decide

theorem compilation_requires_both_branches :
    IsAdmissible {statementSpecification, dependencyOrder, admissibility,
      topologicalSchedule, proofEvidence} certifiedCompilation ∧
    ¬ IsAdmissible {statementSpecification, dependencyOrder, admissibility,
      topologicalSchedule} certifiedCompilation ∧
    ¬ IsAdmissible {statementSpecification, dependencyOrder, admissibility,
      proofEvidence} certifiedCompilation := by
  decide

def schedule : List Archetype :=
  [statementSpecification, dependencyOrder, admissibility,
    topologicalSchedule, proofEvidence, certifiedCompilation]

def alternateSchedule : List Archetype :=
  [statementSpecification, proofEvidence, dependencyOrder,
    admissibility, topologicalSchedule, certifiedCompilation]

theorem schedule_valid : ValidSchedule ∅ schedule := by decide

theorem alternateSchedule_valid : ValidSchedule ∅ alternateSchedule := by decide

theorem schedules_complete :
    schedule.toFinset = Finset.univ ∧ alternateSchedule.toFinset = Finset.univ := by decide

theorem schedules_distinct : schedule ≠ alternateSchedule := by decide

theorem reversed_protocol_compiles :
    InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ schedule.reverse =
      some alternateSchedule := by decide

theorem compiled_protocol_fixed :
    InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ alternateSchedule =
      some alternateSchedule :=
  InfoGeometry.Causal.FiniteDependencyCompiler.compile_of_valid alternateSchedule_valid

end DeclaredProtocol

section DevelopmentBridge

open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Causal.VerifiedDevelopmentState

variable {Node : Type*} (graph : ProofDAG Node) [DecidableEq (AsPoset graph)]

def toDevelopmentState {statement : AsPoset graph → Prop}
    (state : CertifiedState statement) : VerifiedState graph where
  carrier := (state.environment : Set (AsPoset graph))
  dependency_closed := fun precedes membership => state.dependency_closed precedes membership

omit [DecidableEq (AsPoset graph)] in
theorem development_membership_has_proof {statement : AsPoset graph → Prop}
    (state : CertifiedState statement) (target : AsPoset graph)
    (membership : target ∈ (toDevelopmentState graph state).carrier) : statement target :=
  state.proofs target membership

theorem certified_admission_extends_development {statement : AsPoset graph → Prop}
    (state : CertifiedState statement) (target : AsPoset graph)
    (ready : IsReady state.environment target) (proof : statement target) :
    toDevelopmentState graph state ≤
      toDevelopmentState graph (state.extend target ready proof) := by
  intro node membership
  exact Finset.mem_insert_of_mem membership

end DevelopmentBridge

theorem finite_certified_compilation {Node : Type*} [PartialOrder Node]
    [DecidableEq Node] [Fintype Node] (statement : Node → Prop)
    (rules : ProofRules statement) :
    ∃ schedule : List Node, ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧ schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧ ∀ target, statement target := by
  obtain ⟨schedule, valid, distinct, complete, proofs⟩ :=
    finite_proof_compilation statement rules
  refine ⟨schedule, valid, validSchedule_pairwise valid, distinct, ?_, complete, proofs⟩
  have count := validSchedule_card valid
  simpa [complete] using count.symm

theorem executable_certified_compilation {Node : Type*} [PartialOrder Node]
    [DecidableEq Node] [Fintype Node] [DecidableLT Node]
    (statement : Node → Prop) (rules : ProofRules statement)
    (pending : List Node) (distinct : pending.Nodup)
    (coverage : pending.toFinset = Finset.univ) :
    ∃ schedule : List Node,
      InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ pending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧ schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧ ∀ target, statement target := by
  obtain ⟨schedule, computed, valid, unique, complete, length⟩ :=
    InfoGeometry.Causal.FiniteDependencyCompiler.compile_full pending distinct coverage
  have initialProofs : HasProofs statement ∅ := by
    intro target membership
    exact False.elim (Finset.notMem_empty _ membership)
  have resultProofs := validSchedule_preserves_proofs rules initialProofs valid
  refine ⟨schedule, computed, valid, validSchedule_pairwise valid, unique,
    length, complete, ?_⟩
  intro target
  apply resultProofs target
  simp [complete]

end InfoGeometry.MetaCompiler
