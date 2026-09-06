/-
InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean

Five-graded extension and projected information accounting.

This module formalizes the algebraic statement:

A genuine five-graded Lie algebra closes by degree addition. A three-grade
observer may nevertheless see a defect after projecting away the grade-two
memory/contact sector.

The hidden memory is split into negative and positive grade-two channels. The
key theorem is:

  observed defect = projection of total hidden grade-two memory.

This is the formal socket for:

  apparent information loss = projection away from the grade-two ledger.

It does not claim a full black-hole information-paradox solution. Recovery,
unitarity, horizon reconstruction, or Page-curve statements require additional
model-specific witnesses.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-! ## 1. Genuine five-graded Lie algebra socket -/

/--
A genuine five-grading on a Lie algebra.

The intended decomposition is

`L = g_-2 ⊕ g_-1 ⊕ g_0 ⊕ g_+1 ⊕ g_+2`.

The bracket obeys degree addition. In particular,

`[g_-1, g_+1] ⊆ g_0`.

Grade-two memory is not produced by violating this law. It enters through
same-grade brackets, cocycles, contact terms, or projected observer readouts.
-/
structure FiveGrading
    (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  gNegTwo : Submodule ℝ L
  gNegOne : Submodule ℝ L
  gZero : Submodule ℝ L
  gPosOne : Submodule ℝ L
  gPosTwo : Submodule ℝ L

  decomposition_law : Prop
  decomposition_law_holds : decomposition_law

  /-- `[g₋₁, g₋₁] ⊆ g₋₂`. -/
  bracket_negOne_negOne :
    ∀ X Y : L, X ∈ gNegOne → Y ∈ gNegOne → ⁅X, Y⁆ ∈ gNegTwo

  /-- `[g₊₁, g₊₁] ⊆ g₊₂`. -/
  bracket_posOne_posOne :
    ∀ X Y : L, X ∈ gPosOne → Y ∈ gPosOne → ⁅X, Y⁆ ∈ gPosTwo

  /-- `[g₋₁, g₊₁] ⊆ g₀`. -/
  bracket_negOne_posOne :
    ∀ X Y : L, X ∈ gNegOne → Y ∈ gPosOne → ⁅X, Y⁆ ∈ gZero

  /-- `[g₋₂, g₊₂] ⊆ g₀`. -/
  bracket_negTwo_posTwo :
    ∀ X Y : L, X ∈ gNegTwo → Y ∈ gPosTwo → ⁅X, Y⁆ ∈ gZero

namespace FiveGrading

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (G : FiveGrading L)

theorem negOne_posOne_mem_zero
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.bracket_negOne_posOne X Y hX hY

theorem posOne_posOne_mem_posTwo
    {X Y : L}
    (hX : X ∈ G.gPosOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gPosTwo :=
  G.bracket_posOne_posOne X Y hX hY

theorem negOne_negOne_mem_negTwo
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gNegOne) :
    ⁅X, Y⁆ ∈ G.gNegTwo :=
  G.bracket_negOne_negOne X Y hX hY

end FiveGrading

/-! ## 2. Projected three-grade observer with hidden grade-two memory -/

/--
Five-grade projected accounting.

`neg x` and `pos y` are genuine grade `-1` and `+1` representatives.

Their true Lie bracket lands in grade zero.

The observer, however, sees an accounting/readout that includes a hidden
grade-two memory contribution. This is where apparent closure defects, entropy,
heat, or horizon memory are recorded.
-/
structure FiveGradeProjectedAccounting
    (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    (G : FiveGrading L) where

  /-- Grade `-1` representative. -/
  neg : J →ₗ[ℝ] L

  /-- Grade `+1` representative. -/
  pos : J →ₗ[ℝ] L

  neg_mem :
    ∀ x : J, neg x ∈ G.gNegOne

  pos_mem :
    ∀ x : J, pos x ∈ G.gPosOne

  /-- True grade-zero bracket component, defined by the genuine Lie bracket. -/
  zeroPart : J → J → L :=
    fun x y => ⁅neg x, pos y⁆

  /-- Hidden negative grade-two memory/contact component. -/
  hiddenNegTwo : J → J → L

  /-- Hidden positive grade-two memory/contact component. -/
  hiddenPosTwo : J → J → L

  hiddenNegTwo_mem :
    ∀ x y : J, hiddenNegTwo x y ∈ G.gNegTwo

  hiddenPosTwo_mem :
    ∀ x y : J, hiddenPosTwo x y ∈ G.gPosTwo

  /-- Observable projection/readout. -/
  obs : L →ₗ[ℝ] Obs

  /-- Expected three-grade observable contribution. -/
  expectedObs : J → J → Obs

  expected_eq_obs_zero :
    ∀ x y : J,
      expectedObs x y = obs (zeroPart x y)

  /--
  The observer's effective cross readout includes hidden grade-two memory.

  This is not the true Lie bracket. It is the projected/accounting readout.
  -/
  observedCross : J → J → Obs

  observedCross_eq :
    ∀ x y : J,
      observedCross x y = obs (zeroPart x y + hiddenNegTwo x y + hiddenPosTwo x y)

namespace FiveGradeProjectedAccounting

variable
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {G : FiveGrading L}

variable (A : FiveGradeProjectedAccounting J L Obs G)

/-- The total hidden grade-two memory component. -/
def hiddenTotal
    (x y : J) : L :=
  A.hiddenNegTwo x y + A.hiddenPosTwo x y

/--
The true bracket of `g₋₁` and `g₊₁` representatives lands in grade zero.
-/
theorem true_bracket_mem_zero
    (x y : J) :
    ⁅A.neg x, A.pos y⁆ ∈ G.gZero := by
  exact G.negOne_posOne_mem_zero (A.neg_mem x) (A.pos_mem y)

/--
Observed three-grade defect.

This is what the truncated observer interprets as Ricci flux, heat, anomaly,
or information loss.
-/
def observedDefect
    (x y : J) : Obs :=
  A.observedCross x y - A.expectedObs x y

/--
The observed defect is exactly the observable shadow of hidden grade-two memory.
-/
theorem observedDefect_eq_obs_hidden
    (x y : J) :
    A.observedDefect x y = A.obs (A.hiddenTotal x y) := by
  dsimp [observedDefect]
  rw [A.observedCross_eq x y]
  rw [A.expected_eq_obs_zero x y]
  calc
    A.obs (A.zeroPart x y + A.hiddenNegTwo x y + A.hiddenPosTwo x y) -
        A.obs (A.zeroPart x y)
        =
      A.obs (A.zeroPart x y + A.hiddenTotal x y) -
        A.obs (A.zeroPart x y) := by
        dsimp [hiddenTotal]
        rw [add_assoc]
    _ = (A.obs (A.zeroPart x y) + A.obs (A.hiddenTotal x y)) -
        A.obs (A.zeroPart x y) := by
        rw [map_add]
    _ = A.obs (A.hiddenTotal x y) := by
        abel

/--
If hidden grade-two memory is invisible to the observer, the observed defect
vanishes.
-/
theorem observedDefect_eq_zero_of_hidden_invisible
    (x y : J)
    (hhidden : A.obs (A.hiddenTotal x y) = 0) :
    A.observedDefect x y = 0 := by
  rw [A.observedDefect_eq_obs_hidden x y, hhidden]

/--
If the hidden grade-two memory has nonzero observable shadow, then the
three-grade observer sees a nonzero defect.
-/
theorem observedDefect_ne_zero_of_obs_hidden_ne_zero
    (x y : J)
    (hhidden : A.obs (A.hiddenTotal x y) ≠ 0) :
    A.observedDefect x y ≠ 0 := by
  rw [A.observedDefect_eq_obs_hidden x y]
  exact hhidden

/--
The observer sees a nonzero defect exactly when the hidden grade-two component
has nonzero observable projection.
-/
theorem observed_defect_ne_zero_iff_obs_hidden_ne_zero
    (x y : J) :
    A.observedDefect x y ≠ 0 ↔
      A.obs (A.hiddenTotal x y) ≠ 0 := by
  rw [A.observedDefect_eq_obs_hidden x y]

end FiveGradeProjectedAccounting

/-! ## 3. Black-hole information ledger interpretation -/

/--
A black-hole information ledger interpretation.

The hidden grade-two part is interpreted as horizon/contact/memory data.

This is a witness, not a theorem of five-graded algebra alone.
-/
structure BlackHoleInformationLedger
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    (A : FiveGradeProjectedAccounting J L Obs G) where

  /-- Memory readout of the hidden grade-two sector. -/
  memoryReadout : L →ₗ[ℝ] Memory

  /--
  Nonzero memory readout implies nonzero hidden grade-two sum.
  -/
  hidden_part_stored_as_memory :
    ∀ x y : J,
      memoryReadout (A.hiddenTotal x y) ≠ 0 →
        A.hiddenTotal x y ≠ 0

  /--
  Full-ledger conservation/recoverability certificate.

  This is where a concrete model supplies unitarity, Page-curve, holographic
  reconstruction, or equivalent recovery data.
  -/
  full_ledger_recovery_law : Prop
  full_ledger_recovery_law_holds : full_ledger_recovery_law

  /-- Horizon-memory interpretation certificate. -/
  horizon_memory_law : Prop
  horizon_memory_law_holds : horizon_memory_law

namespace BlackHoleInformationLedger

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}

variable (B : BlackHoleInformationLedger J L Obs Memory A)

/-- Hidden grade-two sum. -/
def hiddenGradeTwoSum
    (_B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : L :=
  A.hiddenTotal x y

/-- Visible projection of hidden grade-two memory. -/
def visibleHiddenProjection
    (B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : Obs :=
  A.obs (hiddenGradeTwoSum B x y)

/--
Observed defect is the visible projection of hidden grade-two memory.
-/
theorem observedDefect_eq_visibleHiddenProjection
    (x y : J) :
    A.observedDefect x y =
      visibleHiddenProjection B x y :=
  A.observedDefect_eq_obs_hidden x y

/--
Observed defect is nonzero iff the hidden grade-two memory has nonzero visible
projection.
-/
theorem observedDefect_ne_zero_iff_visibleHidden_ne_zero
    (x y : J) :
    A.observedDefect x y ≠ 0 ↔
      visibleHiddenProjection B x y ≠ 0 :=
  A.observed_defect_ne_zero_iff_obs_hidden_ne_zero x y

/-- Nonzero memory readout implies nonzero hidden grade-two sum. -/
theorem hiddenGradeTwoSum_ne_zero_of_memoryReadout_ne_zero
    (x y : J)
    (hmem : B.memoryReadout (hiddenGradeTwoSum B x y) ≠ 0) :
    hiddenGradeTwoSum B x y ≠ 0 :=
  B.hidden_part_stored_as_memory x y hmem

/-- Stored full recovery law. -/
theorem full_ledger_recovery_valid :
    B.full_ledger_recovery_law :=
  B.full_ledger_recovery_law_holds

end BlackHoleInformationLedger

/-! ## 4. Visible/memory conservation ledger -/

/--
A two-channel information ledger over a five-graded extension.

`visible` is the exterior/three-grade readout.

`memory` is the hidden grade-two/horizon readout.

`total` is the full extended readout.
-/
structure VisibleMemoryLedger
    (State Info : Type*) [AddCommGroup Info] where
  total : State → Info
  visible : State → Info
  memory : State → Info

  evolution : ℝ → State → State

  total_eq_visible_plus_memory :
    ∀ s : State,
      total s = visible s + memory s

  total_conserved :
    ∀ t s,
      total (evolution t s) = total s

namespace VisibleMemoryLedger

variable {State Info : Type*} [AddCommGroup Info]
variable (L : VisibleMemoryLedger State Info)

/-- Exterior/visible information loss. -/
def visibleLoss
    (t : ℝ)
    (s : State) : Info :=
  L.visible s - L.visible (L.evolution t s)

/-- Hidden grade-two memory gain. -/
def memoryGain
    (t : ℝ)
    (s : State) : Info :=
  L.memory (L.evolution t s) - L.memory s

/--
If total information is conserved and decomposes as visible plus memory, then
visible loss equals hidden memory gain.
-/
theorem visibleLoss_eq_memoryGain
    (t : ℝ)
    (s : State) :
    L.visibleLoss t s = L.memoryGain t s := by
  dsimp [visibleLoss, memoryGain]
  have h0 := L.total_eq_visible_plus_memory s
  have h1 := L.total_eq_visible_plus_memory (L.evolution t s)
  have hc := L.total_conserved t s
  have h :
      L.visible (L.evolution t s) +
          L.memory (L.evolution t s)
        =
      L.visible s + L.memory s := by
    rw [← h1, hc, h0]
  have h' :=
    congrArg
      (fun z : Info => z - L.visible (L.evolution t s) - L.memory s)
      h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'.symm

end VisibleMemoryLedger

/-! ## 5. Central-extension alternative -/

/--
A central-extension absorption of a projected three-grade defect.

Instead of enlarging to a five-graded exceptional/contact algebra, one may keep
the three-grade algebra and add a central extension.
-/
structure CentralExtensionAbsorption
    (J L Center Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Center] [Module ℝ Center]
    [AddCommGroup Obs] [Module ℝ Obs] where

  bracket : L → L → L
  neg : J →ₗ[ℝ] L
  pos : J →ₗ[ℝ] L
  expectedZero : J → J → L

  centralDefect : J → J → Center
  centralToObs : Center →ₗ[ℝ] Obs

  /-- Observed three-grade defect. -/
  observedDefect : J → J → Obs

  /--
  Central-extension closure law.

  The projected bracket closes only after adding central charge.
  -/
  observedDefect_eq_central :
    ∀ x y : J,
      observedDefect x y = centralToObs (centralDefect x y)

  /-- Interpretation: central charge stores anomaly/heat/memory residue. -/
  central_charge_memory_law : Prop
  central_charge_memory_law_holds : central_charge_memory_law

namespace CentralExtensionAbsorption

variable
    {J L Center Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Center] [Module ℝ Center]
    [AddCommGroup Obs] [Module ℝ Obs]

variable (C : CentralExtensionAbsorption J L Center Obs)

/--
The observed defect is the observable image of a central charge.
-/
theorem defect_is_central_observable
    (x y : J) :
    C.observedDefect x y = C.centralToObs (C.centralDefect x y) :=
  C.observedDefect_eq_central x y

end CentralExtensionAbsorption

/-! ## 6. Owner target -/

/--
Owner target for projected five-grade information accounting.

Once a projected five-grade accounting witness is supplied, the observed defect
equals the projection of the hidden grade-two memory.
-/
def FiveGradedInformationLedgerOwnerTarget : Prop :=
  ∀ (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs],
  ∀ G : FiveGrading L,
  ∀ A : FiveGradeProjectedAccounting J L Obs G,
  ∀ x y : J,
    A.observedDefect x y = A.obs (A.hiddenTotal x y)

/--
The owner target follows from the supplied projected accounting witness.
-/
theorem fiveGradedInformationLedgerOwnerTarget :
    FiveGradedInformationLedgerOwnerTarget := by
  intro J L Obs _ _ _ _ _ _ _ _ G A x y
  exact A.observedDefect_eq_obs_hidden x y

end InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
