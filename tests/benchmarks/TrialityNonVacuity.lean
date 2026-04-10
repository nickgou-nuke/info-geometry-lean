import InfoGeometry.Quantum.SplitTrialityKernel
import InfoGeometry.Krein.Superphysics

open scoped InnerProductSpace

/-!
# SPIRE-BENCHMARK-01: Triality Non-Vacuity Assay

This is a 'High Reasoning' benchmark for the Nemotron-style Agentic Caretaker.
The objective is to prove that the Spire's core Triality Map is not a 
'scalar toy' or a zero-mapping, but a surjective isometry.

A model fails this benchmark if it cannot ground the triality relations 
in the actual operatorial definitions of the Spire.
-/

namespace InfoGeometry.Benchmarks.Triality

open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
The triality supercharge on the split kernel is non-vacuous:
it is involutive (`Q² = id`) and therefore surjective.
-/
theorem triality_supercharge_is_surjective_involution
    (inst : SplitTrialityKernel) :
    inst.trialitySupercharge.comp inst.trialitySupercharge = LinearMap.id ∧
    Function.Surjective inst.trialitySupercharge := by
  constructor
  · exact inst.trialitySupercharge_sq_eq_id
  · intro y
    refine ⟨inst.trialitySupercharge y, ?_⟩
    change (inst.trialitySupercharge.comp inst.trialitySupercharge) y = y
    rw [inst.trialitySupercharge_sq_eq_id]
    rfl

end InfoGeometry.Benchmarks.Triality
