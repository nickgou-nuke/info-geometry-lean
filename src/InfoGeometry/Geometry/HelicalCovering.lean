/-
InfoGeometry/Geometry/HelicalCovering.lean

Helical covering and monodromy accounting.

The circular quotient forgets how many times modular phase winds.
The helical cover remembers the winding number.

This module formalizes the conserved winding/monodromy charge that prevents
ordinary admissible flow from collapsing a zero-sheet state into a branch
singularity, and prevents nonzero winding sectors from relaxing to the flat
zero sheet.

Analytic identifications, such as log-zeta branch behavior, are supplied later
as calibration data.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.TopologicalSnap

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Geometry.HelicalCovering

open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. Helical covering data -/

/--
A helical covering over a base space.

`project` forgets sheet data.

`winding` records the integer sheet/monodromy charge.

`branchLocus` is the base singular/branch locus.  The key calibration field says
that any lift lying over the branch locus must carry nonzero winding.  This is
the formal way to say that the zero sheet cannot simply collapse into the
branch point while the winding invariant is preserved.
-/
structure HelicalCovering
    (Base Cover : Type*) where
  /-- Projection from the helical cover to the circular/base quotient. -/
  project : Cover → Base

  /-- Integer sheet/winding/monodromy charge. -/
  winding : Cover → ℤ

  /-- Branch/singular locus in the base. -/
  branchLocus : Set Base

  /--
  Branch-locus lifts carry nonzero winding.

  This is a calibration field.  Concrete models may prove it from logarithmic
  branch behavior, spectral divisor data, or a projective singularity theorem.
  -/
  branch_requires_nonzero_winding :
    ∀ x : Cover,
      project x ∈ branchLocus →
        winding x ≠ 0

namespace HelicalCovering

variable {Base Cover : Type*}
variable (C : HelicalCovering Base Cover)

/-- The zero sheet of the helical cover. -/
def zeroSheet : Set Cover :=
  {x : Cover | C.winding x = 0}

/-- The nonzero-winding sector. -/
def nonzeroWindingSector : Set Cover :=
  {x : Cover | C.winding x ≠ 0}

/-- A lift is over the branch locus when its projection lands in `branchLocus`. -/
def LiesOverBranch
    (x : Cover) : Prop :=
  C.project x ∈ C.branchLocus

/-- A zero-sheet point cannot lie over the branch locus. -/
theorem zeroSheet_not_over_branch
    {x : Cover}
    (hx : x ∈ C.zeroSheet) :
    ¬ C.LiesOverBranch x := by
  intro hbranch
  exact C.branch_requires_nonzero_winding x hbranch hx

end HelicalCovering

/-! ## 2. Winding-preserving flows -/

/--
An admissible flow on the helical cover.

The essential field is `preserves_winding`: ordinary admissible flow preserves
the monodromy charge.
-/
structure WindingPreservingFlow
    {Base Cover : Type*}
    (C : HelicalCovering Base Cover) where
  /-- Flow on the helical cover. -/
  flow : ℝ → Cover → Cover

  /-- Zero-time law. -/
  flow_zero :
    ∀ x : Cover, flow 0 x = x

  /-- Additive flow law. -/
  flow_add :
    ∀ s t x, flow (s + t) x = flow s (flow t x)

  /-- Winding/monodromy charge is conserved by admissible flow. -/
  preserves_winding :
    ∀ t x, C.winding (flow t x) = C.winding x

namespace WindingPreservingFlow

variable {Base Cover : Type*}
variable {C : HelicalCovering Base Cover}
variable (F : WindingPreservingFlow C)

/-- Admissible flow preserves the zero sheet. -/
theorem preserves_zeroSheet
    {x : Cover}
    (hx : x ∈ C.zeroSheet)
    (t : ℝ) :
    F.flow t x ∈ C.zeroSheet := by
  dsimp [HelicalCovering.zeroSheet] at hx ⊢
  rw [F.preserves_winding t x]
  exact hx

/-- Admissible flow preserves nonzero winding. -/
theorem preserves_nonzeroWinding
    {x : Cover}
    (hx : x ∈ C.nonzeroWindingSector)
    (t : ℝ) :
    F.flow t x ∈ C.nonzeroWindingSector := by
  dsimp [HelicalCovering.nonzeroWindingSector] at hx ⊢
  rw [F.preserves_winding t x]
  exact hx

/-- A zero-sheet state cannot flow into the branch locus. -/
theorem zeroSheet_cannot_flow_to_branch
    {x : Cover}
    (hx : x ∈ C.zeroSheet)
    (t : ℝ) :
    ¬ C.LiesOverBranch (F.flow t x) := by
  apply C.zeroSheet_not_over_branch
  exact F.preserves_zeroSheet hx t

/-- A nonzero-winding state cannot flow into the zero sheet. -/
theorem nonzero_cannot_flow_to_zeroSheet
    {x : Cover}
    (hx : x ∈ C.nonzeroWindingSector)
    (t : ℝ) :
    F.flow t x ∉ C.zeroSheet := by
  intro hzero
  have hnonzero :
      C.winding (F.flow t x) ≠ 0 :=
    F.preserves_nonzeroWinding hx t
  exact hnonzero hzero

/--
The helical winding flow is an instance of the generic `TopologicalSnap`
obstruction flow, with the zero sheet as the flat sector.
-/
def toConservedObstructionFlow :
    ConservedObstructionFlow Cover ℤ where
  invariant := C.winding
  Flat := C.zeroSheet
  flow := F.flow
  flat_invariant_zero := by
    intro x hx
    exact hx
  flow_preserves_invariant := F.preserves_winding

/--
TopologicalSnap consequence: a nonzero-winding sector cannot relax into the
zero sheet under an admissible winding-preserving flow.
-/
theorem topologicalSnap_no_relaxation_to_zeroSheet
    {x : Cover}
    (hx : C.winding x ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ C.zeroSheet :=
  (F.toConservedObstructionFlow).nontrivial_cannot_flow_to_flat hx t

end WindingPreservingFlow

/-! ## 3. Deck transformations and snap moves -/

/--
A deck action on the helical cover.

A deck transformation changes the winding by an integer while preserving the
base projection.  This is the formal version of moving between sheets.
-/
structure DeckAction
    {Base Cover : Type*}
    (C : HelicalCovering Base Cover) where
  /-- Deck transformation indexed by integer sheet shift. -/
  deck : ℤ → Cover → Cover

  /-- Deck transformations preserve the base projection. -/
  project_deck :
    ∀ n x, C.project (deck n x) = C.project x

  /-- Deck transformations shift winding by `n`. -/
  winding_deck :
    ∀ n x, C.winding (deck n x) = C.winding x + n

  /-- Zero deck transformation is identity. -/
  deck_zero :
    ∀ x, deck 0 x = x

  /-- Additive deck law. -/
  deck_add :
    ∀ m n x, deck (m + n) x = deck m (deck n x)

namespace DeckAction

variable {Base Cover : Type*}
variable {C : HelicalCovering Base Cover}
variable (D : DeckAction C)

/-- One positive sheet step. -/
def step
    (x : Cover) : Cover :=
  D.deck 1 x

/-- One negative sheet step. -/
def stepInv
    (x : Cover) : Cover :=
  D.deck (-1) x

/-- A positive sheet step increases winding by one. -/
theorem winding_step
    (x : Cover) :
    C.winding (D.step x) = C.winding x + 1 :=
  D.winding_deck 1 x

/-- A negative sheet step decreases winding by one. -/
theorem winding_stepInv
    (x : Cover) :
    C.winding (D.stepInv x) = C.winding x - 1 := by
  dsimp [stepInv]
  simpa [sub_eq_add_neg] using D.winding_deck (-1) x

/-- Deck moves preserve the base projection. -/
theorem project_step
    (x : Cover) :
    C.project (D.step x) = C.project x :=
  D.project_deck 1 x

end DeckAction

/-! ## 4. Monodromy events -/

/--
A monodromy event is a closed base motion whose lift changes sheet.

`charge` is the resulting winding shift.
-/
structure MonodromyEvent
    {Base Cover : Type*}
    (C : HelicalCovering Base Cover) where
  /-- Starting point on the helical cover. -/
  start : Cover

  /-- Ending point on the helical cover. -/
  finish : Cover

  /-- The projection closes in the base. -/
  projection_closed :
    C.project finish = C.project start

  /-- Winding shift / monodromy charge. -/
  charge : ℤ

  /-- Winding change law. -/
  winding_change :
    C.winding finish = C.winding start + charge

namespace MonodromyEvent

variable {Base Cover : Type*}
variable {C : HelicalCovering Base Cover}
variable (M : MonodromyEvent C)

/-- Nontrivial monodromy cannot end at the same lifted point. -/
theorem finish_ne_start_of_charge_ne_zero
    (hcharge : M.charge ≠ 0) :
    M.finish ≠ M.start := by
  intro hsame
  have hwind :
      C.winding M.start = C.winding M.start + M.charge := by
    simpa [hsame] using M.winding_change
  have hzero : M.charge = 0 := by
    omega
  exact hcharge hzero

end MonodromyEvent

/-! ## 5. Sheet packets -/

/--
A packet of sheet amplitudes/readouts.

This is the abstract socket for statements such as:

`Ψ = Σ_N c_N |N⟩`.

No summability or Hilbert structure is asserted here.
-/
structure SheetPacket
    (Cover Amplitude : Type*) where
  /-- State/lift on a given sheet. -/
  stateOnSheet : ℤ → Cover

  /-- Amplitude/readout attached to each sheet. -/
  amplitude : ℤ → Amplitude

/-! ## 6. Spectral divisor / logarithmic monodromy calibration -/

/--
Calibration from a spectral divisor to a helical branch locus.

This is the correct abstraction for zeta/L-function applications:

a zero or pole of a spectral function is not automatically a branch point of
the function itself, but it is a branch/monodromy point for a chosen logarithmic
or phase readout.
-/
structure SpectralDivisorMonodromyCalibration
    (Spectral Base Cover : Type*)
    (C : HelicalCovering Base Cover) where
  /-- Spectral divisor, e.g. zero/pole/resonance locus. -/
  spectralDivisor : Set Spectral

  /-- Logarithmic or phase readout into the base. -/
  logPhaseReadout : Spectral → Base

  /-- Divisor points map to the branch locus for the chosen readout. -/
  divisor_maps_to_branch :
    ∀ s : Spectral,
      s ∈ spectralDivisor →
        logPhaseReadout s ∈ C.branchLocus

namespace SpectralDivisorMonodromyCalibration

variable {Spectral Base Cover : Type*}
variable {C : HelicalCovering Base Cover}
variable (S : SpectralDivisorMonodromyCalibration Spectral Base Cover C)

/--
A spectral divisor point lands in the branch locus of the logarithmic/phase
readout.
-/
theorem maps_to_branch
    {s : Spectral}
    (hs : s ∈ S.spectralDivisor) :
    S.logPhaseReadout s ∈ C.branchLocus :=
  S.divisor_maps_to_branch s hs

end SpectralDivisorMonodromyCalibration

/-! ## 7. Owner targets -/

/-- Owner target for helical-cover branch exclusion on the zero sheet. -/
def HelicalCoveringOwnerTarget
    (Base Cover : Type*) : Prop :=
  ∀ C : HelicalCovering Base Cover,
    ∀ x : Cover,
      x ∈ C.zeroSheet →
        ¬ C.LiesOverBranch x

/-- The helical-cover owner target is the zero-sheet branch exclusion law. -/
theorem helicalCoveringOwnerTarget
    (Base Cover : Type*) :
    HelicalCoveringOwnerTarget Base Cover := by
  intro C x hx
  exact C.zeroSheet_not_over_branch hx

/-- Owner target for deck/monodromy readout laws on a supplied helical cover. -/
def DeckActionOwnerTarget
    {Base Cover : Type*}
    (C : HelicalCovering Base Cover) : Prop :=
  ∀ D : DeckAction C,
    (∀ x : Cover, C.project (D.step x) = C.project x) ∧
      (∀ x : Cover, C.winding (D.step x) = C.winding x + 1) ∧
        (∀ x : Cover, C.winding (D.stepInv x) = C.winding x - 1)

/-- A deck action supplies the projection and winding readouts for sheet steps. -/
theorem deckActionOwnerTarget
    {Base Cover : Type*}
    (C : HelicalCovering Base Cover) :
    DeckActionOwnerTarget C := by
  intro D
  exact ⟨
    (fun x => D.project_step x),
    (fun x => D.winding_step x),
    (fun x => D.winding_stepInv x)⟩

/-- Owner target for spectral-divisor monodromy calibration readout. -/
def SpectralDivisorMonodromyOwnerTarget
    (Spectral Base Cover : Type*) : Prop :=
  ∀ C : HelicalCovering Base Cover,
    ∀ S : SpectralDivisorMonodromyCalibration Spectral Base Cover C,
      ∀ s : Spectral,
        s ∈ S.spectralDivisor →
          S.logPhaseReadout s ∈ C.branchLocus

/-- A spectral-divisor calibration supplies the branch-locus readout. -/
theorem spectralDivisorMonodromyOwnerTarget
    (Spectral Base Cover : Type*) :
    SpectralDivisorMonodromyOwnerTarget Spectral Base Cover := by
  intro C S s hs
  exact S.maps_to_branch hs

end InfoGeometry.Geometry.HelicalCovering
