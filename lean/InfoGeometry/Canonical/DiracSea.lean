import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ModularNilpotentAutomorphism
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorFockSpace
import InfoGeometry.Topology.FractalCantorFockWitness

/-!
# InfoGeometry.Canonical.DiracSea

A theorem-safe finite-stage bridge from the existing finite nilpotent modular
seed to the Cantor/Fock carrier narrative.

Important scope note:
This lane is formalized over the existing `ℕ → Bool` Cantor boundary and finite
prefix reconstruction already present in the repo. It does not claim a completed
bi-infinite Hilbert completion; it packages the stable, finite-stage,
combinatorial core as a reusable bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiracSea

open Matrix
open InfoGeometry.Canonical.SplitCliffordSourceWickBase
open InfoGeometry.Canonical.ModularNilpotentAutomorphism
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.CantorFockSpace

/-- Carrier abstraction for a single-step Dirac-sea generator. -/
abbrev DiracSeaOperator (Op : Type*) [Ring Op] := Op

/-- The carrier step is the same square-zero modular seed (`N`). -/
def step : M2R := SplitCliffordSourceWickBase.N

/-- Strictly nilpotent step law: `N² = 0`. -/
@[simp] theorem step_sq_zero : step * step = (0 : M2R) := by
  simp [step, N_sq_zero]

/-- Combinatorial free-energy functional in the same sector: `A_info = N - N`. -/
def informationFreeEnergy : M2R := step - step

/-- Exact zero in this sector: `A_info = 0`. -/
@[simp] theorem informationFreeEnergy_eq_zero : informationFreeEnergy = (0 : M2R) := by
  simp [informationFreeEnergy]

/-- Modular-flux recasting to the existing modular names. -/
theorem entropyFlux_eq_step : entropyFlux = step := by
  exact
    (ModularNilpotentAutomorphism.entropyFlux_eq_N : entropyFlux = SplitCliffordSourceWickBase.N)

theorem modular_informationFreeEnergy_eq_zero :
    ModularNilpotentAutomorphism.informationFreeEnergy = (0 : M2R) :=
  ModularNilpotentAutomorphism.informationFreeEnergy_eq_zero

/-- Minimal Dirac-sea package used by this bridge. -/
structure DiracSeaAlgebra (Op : Type*) [Ring Op] where
  generator : Op
  generator_sq_zero : generator * generator = 0

/-- Canonical extraction of the square-zero Dirac-sea algebra from the finite Wick atom. -/
def canonicalDiracSea : DiracSeaAlgebra M2R where
  generator := step
  generator_sq_zero := step_sq_zero

/-- Carrier notation aligned with the existing Cantor boundary API. -/
abbrev InfiniteDiracBoundary := InfiniteBinaryWordSpace

/-- Canonical (all-zero) boundary word used for the finite-prefix vacuum readout. -/
abbrev diracVacuumBoundary : InfiniteDiracBoundary := vacuumBoundary

/-- Vacuum-prefix state embedding into the witness Hilbert carrier. -/
def diracVacuumPrefixState
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteFockCarrierData E) (n : ℕ) : E :=
  cantorVacuumPrefixState (W := W) n

/-- The vacuum-prefix at depth zero is the empty-cylinder basis vector. -/
theorem diracVacuumPrefixState_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteFockCarrierData E) :
    diracVacuumPrefixState (W := W) 0 = W.hilbertCarrier.orbitBasis [] := by
  simpa [diracVacuumPrefixState] using (cantorVacuumPrefixState_zero (W := W))

/-- Finite-prefix recursion for the canonical Dirac boundary word. -/
theorem diracVacuumPrefixState_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : CelikKocakInfiniteFockCarrierData E) (n : ℕ) :
    diracVacuumPrefixState (W := W) (n + 1)
      = W.hilbertCarrier.orbitBasis
          (boundaryPrefix (n + 1) diracVacuumBoundary) := by
  simp [diracVacuumPrefixState, diracVacuumBoundary, cantorVacuumPrefixState, cantorPrefixState]

/--
Bi-infinite (formal) Dirac-sea words and interface step.

These names package the occupied/empty interface intuition in a combinatorial form:
`...111|00...` is represented by a `ℤ`-indexed bit string,
with `-1 = true` and `0 = false` at the interface,
and the step `diracSeaStep` maps that profile to `...110|10...`.
Applying twice is nilpotent by construction.
-/
abbrev DiracSeaBoundary := ℤ → Bool

/-- Dirac-sea vacuum profile: occupied on the negative side, empty on nonnegative side. -/
def diracSeaVacuum : DiracSeaBoundary := fun n => n < 0

/-- Interface-only flip: `-1 -> false`, `0 -> true`, others unchanged. -/
def diracSeaInterfaceFlip (w : DiracSeaBoundary) : DiracSeaBoundary :=
  fun n => if n = -1 then false else if n = 0 then true else w n

/-- The boundary-step operator:
`010...` at (`-1`,`0`) triggers the flip, otherwise annihilates to `none`. -/
def diracSeaStep (w : DiracSeaBoundary) : Option DiracSeaBoundary :=
  if _h : w (-1) = true ∧ w 0 = false then
    some (diracSeaInterfaceFlip w)
  else
    none

/-- Vacuum is annihilated by nothing and admits a single-step particle-hole interface move. -/
theorem diracSeaVacuumStep : diracSeaStep diracSeaVacuum = some (diracSeaInterfaceFlip diracSeaVacuum) := by
  have hL : diracSeaVacuum (-1) = true := by
    simp [diracSeaVacuum]
  have hR : diracSeaVacuum 0 = false := by
    simp [diracSeaVacuum]
  simp [diracSeaStep, hL, hR]

/-- Interface-step is nilpotent in the sense `S² = 0` as an `Option`-valued operator. -/
theorem diracSeaStep_square_zero (w : DiracSeaBoundary) :
    Option.bind (diracSeaStep w) diracSeaStep = none := by
  by_cases h : w (-1) = true ∧ w 0 = false
  · rcases h with ⟨hL, hR⟩
    simp [diracSeaStep, diracSeaInterfaceFlip, hL, hR]
  · simp [diracSeaStep, h]

/-- Only interface bits are changed by the local step. -/
theorem diracSeaStep_only_interface (w w' : DiracSeaBoundary)
    (hstep : diracSeaStep w = some w') :
    (w' (-1) = false) ∧ (w' 0 = true) ∧
      (∀ n : ℤ, n ≠ -1 → n ≠ 0 → w' n = w n) := by
  have hcond : w (-1) = true ∧ w 0 = false := by
    by_contra hcond
    simp [diracSeaStep, hcond] at hstep
  have hflip : w' = diracSeaInterfaceFlip w := by
    have h' := hstep
    simp [diracSeaStep, hcond] at h'
    simpa using h'.symm
  subst hflip
  constructor
  · simp [diracSeaInterfaceFlip]
  constructor
  · simp [diracSeaInterfaceFlip]
  · intro n hn1 hn2
    simp [diracSeaInterfaceFlip, hn1, hn2]

/-- The interface condition for the step is exactly the occupied-then-empty pattern. -/
theorem diracSeaStep_eq_none_iff
    (w : DiracSeaBoundary) : diracSeaStep w = none ↔ ¬ (w (-1) = true ∧ w 0 = false) := by
  simp [diracSeaStep]

end InfoGeometry.Canonical.DiracSea
