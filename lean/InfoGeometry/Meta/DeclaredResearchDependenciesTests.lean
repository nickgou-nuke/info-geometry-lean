import InfoGeometry.Meta.MetaEpistemicCompiler

namespace InfoGeometry.MetaCompiler.DeclaredResearchGraph.Tests

open RepoArchetype
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

example : Fintype.card RepoArchetype = 6 := by decide

example : (Finset.univ.filter (IsReady foundation)).card = 2 := by decide

example : ¬ ValidSchedule ∅ schedule.reverse := by decide

example : compile ∅ schedule.reverse = some alternateSchedule := reversed_schedule_compiles

example : compile foundation [metaEpistemicCompiler, souriauKMS, carnotInformation] =
    some [souriauKMS, carnotInformation, metaEpistemicCompiler] := by decide

example : compile foundation [metaEpistemicCompiler, carnotInformation] = none := by decide

example : compile ∅ [qedTwoPoint, qedTwoPoint] = none := by decide

example : ∀ target : RepoArchetype, ¬ target < target := fun target => lt_irrefl target

def ancestorStatement (target : RepoArchetype) : Prop := qedTwoPoint ≤ target

theorem ancestorRules : ProofRules ancestorStatement :=
  fun target _ => qed_is_universal_ancestor target

example : ∃ completed,
    compileCertified ancestorRules (emptyCertifiedState ancestorStatement) schedule.reverse =
      some completed ∧ completed.environment = Finset.univ ∧
        ∀ target, ancestorStatement target :=
  declared_compilation_with_evidence ancestorStatement ancestorRules

example : (compileCertified ancestorRules (emptyCertifiedState ancestorStatement)
    schedule.reverse).map CertifiedState.environment = some Finset.univ := by decide

example : ¬ HasProofs (fun _ : RepoArchetype => (0 : ℕ) = 1) schedule.toFinset :=
  successful_scheduling_does_not_supply_proofs.2

end InfoGeometry.MetaCompiler.DeclaredResearchGraph.Tests
