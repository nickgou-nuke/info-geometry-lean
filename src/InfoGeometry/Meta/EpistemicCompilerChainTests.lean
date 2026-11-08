import InfoGeometry.Meta.EpistemicCompilerChain

namespace InfoGeometry.MetaCompiler.Tests

open InfoGeometry.MetaCompiler

example : Phase.precedes Phase.primaMateriaIntake Phase.kernelCertifiedPromotion := by
  decide

example : ¬ Phase.precedes Phase.kernelCertifiedPromotion Phase.primaMateriaIntake := by
  decide

def openCandidate : TypedArchetype Nat .candidate where
  name := `InfoGeometry.MetaCompiler.Tests.openCandidate
  phase := Phase.toNat Phase.multiAgentCandidateRepair
  claim := fun n => n + 0 = n
  evidence := trivial

def promotedCandidate : TypedArchetype Nat .proved :=
  TypedArchetype.promoteToProved openCandidate (by intro n; change n + 0 = n; exact Nat.add_zero n)

example : promotedCandidate.phase = Phase.toNat Phase.multiAgentCandidateRepair := rfl
example : promotedCandidate.name = `InfoGeometry.MetaCompiler.Tests.openCandidate := rfl

end InfoGeometry.MetaCompiler.Tests
