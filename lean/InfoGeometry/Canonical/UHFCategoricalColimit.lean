import Mathlib
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# The UHF Categorical Colimit
## The Infinite-Dimensional Thermodynamic Limit (UHF / MASA)

By passing the finite diagonal matrices (Cylinder Observables) 
through a sequence of natural inclusions, we construct the continuous 
spectrum of the UHF algebra (Uniformly Hyperfinite). 
We strictly enforce the Colimit Continuum Mandate here: infinite dimensions 
are achieved algebraically via categorical limits (`Ring.DirectLimit`) 
rather than analytic continuation.
-/

namespace InfoGeometry.Canonical.UHFCategoricalColimit

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

-- The sequence of natural inclusions for the kinematic sheets
variable (bonding : ∀ (i j : ℕ), i ≤ j → DiagAlg i →+* DiagAlg j)
variable [DirectedSystem DiagAlg (fun i j h => bonding i j h)]

/-- 
Archetype 1: The Infinite Continuum Space (UHF Colimit).
The categorical inductive direct limit of the finite diagonal layers.
-/
abbrev UHFColimitRing := Ring.DirectLimit DiagAlg (fun i j h => bonding i j h)

/--
Archetype 2: The Stage Injection.
Injects finite-stage observables perfectly into the infinite algebraic colimit.
-/
noncomputable def stageInjection (n : ℕ) : DiagAlg n →+* UHFColimitRing bonding :=
  Ring.DirectLimit.of DiagAlg (fun i j h => bonding i j h) n

/-- 
Archetype 3: The Continuum Vacuum Projection (UHF Identity).
Lifts the unexcited scalar vacuum (the identity matrix observable) 
identically across the entire limit space.
Because the vacuum lives in the constants, it is canonically 
invariant under the tensor tower inclusions.
-/
noncomputable def continuumIdentity (n : ℕ) : UHFColimitRing bonding :=
  stageInjection bonding n 1

/--
Theorem: The Continuum Vacuum is structurally preserved across all stages.
-/
theorem continuumIdentity_is_unit (n : ℕ) :
    continuumIdentity bonding n = 1 := by
  dsimp [continuumIdentity]
  exact (stageInjection bonding n).map_one

end InfoGeometry.Canonical.UHFCategoricalColimit
