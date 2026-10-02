import InfoGeometry.Meta.EpistemicCompilerChain

namespace InfoGeometry.MetaCompiler.Tests

open InfoGeometry.MetaCompiler

example : Phase.precedes Phase.primaMateriaIntake Phase.kernelCertifiedPromotion := by
  decide

example : ¬ Phase.precedes Phase.kernelCertifiedPromotion Phase.primaMateriaIntake := by
  decide

example : Status.label Status.corridorReady = "corridor_ready" := by
  rfl

def provedCandidate : Candidate where
  claim := ∀ n : Nat, n + 0 = n
  phase := Phase.kernelCertifiedPromotion
  status := Status.proved
  owner := "InfoGeometry.MetaCompiler.Tests"
  evidence := by
    intro _
    exact Nat.add_zero

def openCandidate : Candidate where
  claim := ∀ n : Nat, n + 0 = n
  phase := Phase.multiAgentCandidateRepair
  status := Status.corridorReady
  owner := "InfoGeometry.MetaCompiler.Tests"
  evidence := by
    intro impossible
    cases impossible

example : ∃ certified, promote provedCandidate = some certified := by
  exact (promote_proved_accepts provedCandidate rfl).imp (fun certified h => h.1)

example : promote openCandidate = none := by
  exact promote_raw_rejects openCandidate (by decide)

end InfoGeometry.MetaCompiler.Tests
