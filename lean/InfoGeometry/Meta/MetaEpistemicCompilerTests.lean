import InfoGeometry.Meta.MetaEpistemicCompiler

namespace InfoGeometry.MetaCompiler.Tests

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler
open DeclaredProtocol.Archetype

example : compile (∅ : Finset (Fin 0)) [] = some [] := by decide

example : compile (∅ : Finset (Fin 1)) [0] = some [0] := by decide

example : compile (∅ : Finset (Fin 3)) [2, 1, 0] = some [0, 1, 2] := by decide

example : compile (∅ : Finset (Fin 3)) [1, 0, 2] = some [0, 1, 2] := by decide

example : ∀ pending ∈ ([0, 1, 2] : List (Fin 3)).permutations',
    compile ∅ pending = some [0, 1, 2] := by decide

example : compile ({0} : Finset (Fin 3)) [2, 1] = some [1, 2] := by decide

example : compile (Finset.univ : Finset (Fin 3)) [] = some [] := by decide

example : compile (∅ : Finset (Fin 3)) [0, 0, 1, 2] = none := by decide

example : compile (∅ : Finset (Fin 3)) [0, 2] = none := by decide

example : compile ({0} : Finset (Fin 3)) [0, 1, 2] = none := by decide

example : compileWithFuel 2 (∅ : Finset (Fin 3)) [2, 1, 0] = none := by decide

example : compileWithFuel 4 (∅ : Finset (Fin 3)) [2, 1, 0] = some [0, 1, 2] := by decide

example : compile ∅ DeclaredProtocol.schedule.reverse = some DeclaredProtocol.alternateSchedule :=
  DeclaredProtocol.reversed_protocol_compiles

example : compile {statementSpecification} [proofEvidence, dependencyOrder] =
    some [proofEvidence, dependencyOrder] := by decide

example : compile {statementSpecification} [dependencyOrder, proofEvidence] =
    some [dependencyOrder, proofEvidence] := by decide

example : ∀ count : Fin 7,
    ValidSchedule ∅ (DeclaredProtocol.alternateSchedule.take count.val) ∧
      ValidSchedule (DeclaredProtocol.alternateSchedule.take count.val).toFinset
        (DeclaredProtocol.alternateSchedule.drop count.val) := by decide

def initialState : CertifiedState (fun target : Fin 3 => target.val < 3) where
  environment := ∅
  dependency_closed := by
    intro later earlier precedes membership
    exact False.elim (Finset.notMem_empty _ membership)
  proofs := by
    intro target membership
    exact False.elim (Finset.notMem_empty _ membership)

theorem finiteRules : ProofRules (fun target : Fin 3 => target.val < 3) :=
  fun target _ => target.isLt

example : initialState.execute finiteRules [0, 1, 2] (by decide) =
    (initialState.execute finiteRules [0] (by decide)).execute finiteRules [1, 2] (by decide) :=
  CertifiedState.execute_append finiteRules initialState [0] [1, 2] (by decide) (by decide)

example : (compileCertified finiteRules initialState [2, 1, 0]).map
    CertifiedState.environment = some Finset.univ := by decide

example : (compileCertified finiteRules initialState [0, 2]).map
    CertifiedState.environment = none := by decide

example : ∃ completed, compileCertified finiteRules initialState [2, 1, 0] = some completed ∧
    completed.environment = Finset.univ ∧
    HasProofs (fun target : Fin 3 => target.val < 3) Finset.univ := by
  apply compileCertified_proves_target finiteRules initialState Finset.univ [2, 1, 0]
  · exact Finset.empty_subset _
  · intro later earlier precedes membership
    exact Finset.mem_univ earlier
  · decide
  · decide

example : ∃ schedule : List (Fin 3), compile ∅ [2, 1, 0] = some schedule ∧
    ValidSchedule ∅ schedule ∧ schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
    schedule.Nodup ∧ schedule.length = Fintype.card (Fin 3) ∧
    schedule.toFinset = Finset.univ ∧ ∀ target : Fin 3, target.val < 3 :=
  executable_certified_compilation _ finiteRules [2, 1, 0] (by decide) (by decide)

end InfoGeometry.MetaCompiler.Tests
