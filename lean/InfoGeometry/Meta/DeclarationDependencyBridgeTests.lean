import InfoGeometry.Meta.DeclarationDependencyBridge

namespace InfoGeometry.MetaCompiler.DeclarationBridge.Tests

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

def declarationName (node : Fin 2) : Lean.Name :=
  if node = 0 then ``validSchedule_fresh else ``validSchedule_nodup

def declaration : Fin 2 ↪ Lean.Name where
  toFun := declarationName
  inj' := by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all [declarationName]

/-- The selected edge is declared explicitly, not extracted from an environment. -/
def bridge : DependencyCorrespondence (Fin 2) where
  declaration := declaration
  depends prerequisite target :=
    prerequisite = declaration 0 ∧ target = declaration 1
  resolve := by
    intro target prerequisite dependency
    obtain ⟨sourceName, targetName⟩ := dependency
    have targetIsOne : target = 1 := declaration.injective targetName
    subst target
    exact ⟨0, sourceName.symm, by decide⟩

def statement (node : Fin 2) : Prop :=
  if node = 0 then
    ∀ (environment : Finset Nat) (schedule : List Nat),
      ValidSchedule environment schedule →
        ∀ target ∈ schedule, target ∉ environment
  else
    ∀ (environment : Finset Nat) (schedule : List Nat),
      ValidSchedule environment schedule → schedule.Nodup

theorem rules : ProofRules statement := by
  intro node _
  fin_cases node
  · simpa only [statement, if_pos rfl] using
      (fun (environment : Finset Nat) (schedule : List Nat)
        (valid : ValidSchedule environment schedule) => validSchedule_fresh valid)
  · simpa only [statement, show (1 : Fin 2) ≠ 0 by decide, if_false] using
      (fun (environment : Finset Nat) (schedule : List Nat)
        (valid : ValidSchedule environment schedule) => validSchedule_nodup valid)

def initialState : CertifiedState statement where
  environment := ∅
  dependency_closed := by
    intro later earlier precedes membership
    exact False.elim (Finset.notMem_empty _ membership)
  proofs := by
    intro target membership
    exact False.elim (Finset.notMem_empty _ membership)

example : compile (∅ : Finset (Fin 2)) [1, 0] = some [0, 1] := by decide

example : compile (∅ : Finset (Fin 2)) [1] = none := by decide

example : compile (∅ : Finset (Fin 2)) [0, 0, 1] = none := by decide

example : ¬ bridge.Closed {1} := by
  intro closed
  obtain ⟨source, membership, equalName⟩ :=
    closed 1 (by simp) (declaration 0) ⟨rfl, rfl⟩
  have sourceIsOne : source = 1 := Finset.mem_singleton.mp membership
  have sourceIsZero : source = 0 := declaration.injective equalName
  have impossible : (1 : Fin 2) = 0 := sourceIsOne.symm.trans sourceIsZero
  exact (by decide : (1 : Fin 2) ≠ 0) impossible

example : ∀ count, bridge.Closed (([0, 1] : List (Fin 2)).take count).toFinset := by
  intro count
  simpa only [initialState, Finset.empty_union] using
    bridge.prefix_closed initialState.dependency_closed
    (show ValidSchedule initialState.environment [0, 1] by decide) count

theorem real_statements_compiled :
    ∃ completed, compileCertified rules initialState [1, 0] = some completed ∧
      completed.environment = Finset.univ ∧ bridge.Closed completed.environment ∧
      HasProofs statement completed.environment := by
  obtain ⟨completed, computed, complete⟩ :=
    compileCertified_complete rules initialState Finset.univ [1, 0]
      (Finset.empty_subset _)
      (by intro later earlier precedes membership; exact Finset.mem_univ earlier)
      (by decide) (by decide)
  exact ⟨completed, computed, complete,
    bridge.closed_of_isLowerSet completed.dependency_closed, completed.proofs⟩

example : ∃ schedule, compile initialState.environment [1, 0] = some schedule ∧
    ∀ count, bridge.Closed (initialState.environment ∪ (schedule.take count).toFinset) ∧
      HasProofs statement (initialState.environment ∪ (schedule.take count).toFinset) := by
  obtain ⟨completed, computed, _, _, _⟩ := real_statements_compiled
  obtain ⟨schedule, scheduled, _, _, _, _, _, prefixes⟩ :=
    certified_compilation_preserves_named_dependencies bridge rules
      initialState completed [1, 0] computed
  exact ⟨schedule, scheduled, prefixes⟩

#print axioms certified_compilation_preserves_named_dependencies
#print axioms real_statements_compiled

end InfoGeometry.MetaCompiler.DeclarationBridge.Tests
