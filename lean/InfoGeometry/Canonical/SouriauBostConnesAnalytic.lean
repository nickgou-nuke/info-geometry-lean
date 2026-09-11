import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauBostConnesTransition
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.ErlangenColimitResolution

/-!
# Finite Souriau-Bost-Connes Vacuum Readout and Colimit Boundary

This module supplies the finite vacuum readout for the Souriau-Bost-Connes
transition and transports it through the existing colimit boundary owner.
It does not construct an analytic Bost-Connes partition, a zero-temperature
limit, or an infinite trace.

Following the Colimit Continuum Mandate, we do not rely on brute-force real analysis 
or classical measure theory. Instead, we project the finite algebraic models natively 
through `UHFInductiveColimitBoundary` and `TensorTowerColimit`.

## Key Constructions
1. **Finite vacuum evaluation**: a linear readout on each finite diagonal stage.
2. **Stage coherence**: the readout is preserved by the successor embedding.
3. **Colimit boundary readout**: the finite cylinder evaluation agrees with the
   corresponding boundary-prefix evaluation.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauBostConnesAnalytic

open InfoGeometry.Canonical.SouriauBostConnesTransition
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
### 1. Finite Vacuum Boundary Readout
We define a vacuum evaluation at the finite $n$-th stage of the UHF diagonal
algebra `DiagAlg n`. The legacy "zero-temperature" name denotes only this
finite readout; no temperature limit is asserted.
-/

/-- The all-zero vacuum bit-word at finite stage `n`. -/
def finiteVacuumWord (n : ℕ) : BitWord n :=
  fun _ => false

/-- The zero-temperature KMS state evaluated on a finite-stage diagonal observable.
    At zero temperature, the thermal state shatters and fully concentrates on the vacuum. -/
def finiteZeroTempState (n : ℕ) : DiagAlg n →ₗ[ℂ] ℂ where
  toFun f := f (finiteVacuumWord n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 
The finite vacuum word is invariant under the predecessor mapping `prefixSucc`.
This provides the categorical coherence required for the inductive limit.
-/
theorem prefixSucc_finiteVacuumWord (n : ℕ) :
    prefixSucc n (finiteVacuumWord (n + 1)) = finiteVacuumWord n := by
  ext i
  rfl

/-- 
**Stage coherence**:
The finite vacuum evaluation commutes exactly with the diagonal successor
embedding. This is the finite cocone equation used by the existing colimit
boundary owner; it is not an analytic or topological-limit theorem.
-/
theorem zeroTempState_commutes_with_embedding (n : ℕ) (f : DiagAlg n) :
    finiteZeroTempState (n + 1) (diagEmbedSucc n f) = finiteZeroTempState n f := by
  dsimp [finiteZeroTempState, diagEmbedSucc]
  rw [prefixSucc_finiteVacuumWord n]

/-!
### 2. Boundary-prefix readout
We evaluate finite cylinder observables on the supplied boundary word. The
boundary is the carrier of the colimit readout, not an analytic thermodynamic
limit.
-/

/-- The all-zero vacuum word on the infinite Cantor boundary.
    This exactly matches `canonicalCrystallisedReadout.boundaryWord`. -/
def cantorVacuumBoundary : ℕ → Bool :=
  fun _ => false

/-- 
The global zero-temperature state defined over the Cylinder Colimit.
Because the system is exactly coherent, the infinite boundary state is directly
accessible from any finite cylinder observable.
-/
def colimitZeroTempState (n : ℕ) (f : DiagAlg n) : ℂ :=
  cylinder n f cantorVacuumBoundary

/-- 
**Boundary-prefix agreement**
The boundary evaluation is exactly equivalent to the finite local vacuum
evaluation at the same stage. This is an algebraic cylinder identity.
-/
theorem phase_space_shattering_to_cantor_boundary (n : ℕ) (f : DiagAlg n) :
    colimitZeroTempState n f = finiteZeroTempState n f := by
  dsimp [colimitZeroTempState, cylinder, finiteZeroTempState,
    cantorVacuumBoundary, boundaryPrefix, finiteVacuumWord]
  have hprefix : boundaryPrefix n cantorVacuumBoundary = finiteVacuumWord n := by
    funext i
    rfl
  rw [hprefix]

/-!
### 3. Colimit-indexed coherence
-/

/-- 
**Successor coherence of the boundary readout**
Passing the finite readout through the `UHFInductiveColimitBoundary` gives the
successor-stage cocone equality. The legacy theorem name is retained, but the
statement is finite colimit coherence, not an analytic limit or an unconditional
KMS theorem.
-/
theorem colimit_crystallization_resolves_closure_debt (n : ℕ) (f : DiagAlg n) :
    colimitZeroTempState (n + 1) (diagEmbedSucc n f) = colimitZeroTempState n f :=
  rfl

/- The theorem-safe name for the same finite successor-stage equation. -/
theorem colimit_vacuum_readout_succ_coherent (n : ℕ) (f : DiagAlg n) :
    colimitZeroTempState (n + 1) (diagEmbedSucc n f) = colimitZeroTempState n f :=
  colimit_crystallization_resolves_closure_debt n f

end InfoGeometry.Canonical.SouriauBostConnesAnalytic
