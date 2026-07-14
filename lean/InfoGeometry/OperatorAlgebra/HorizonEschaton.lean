/-
InfoGeometry/OperatorAlgebra/HorizonEschaton.lean

Genesis, Revelation, and Mahapralaya as distinct horizon operations.

This module separates three operations:

* Genesis:
    quench/split/individuation into an observable algebra and hidden memory;

* Revelation:
    faithful recovery/unveiling of hidden memory from exterior data;

* Mahapralaya:
    dissolution/de-individuation by collapse of memory distinctions into a
    terminal thermalized state.

The module proves the negative boundaries constructively:

* exterior collapse of distinct hidden memories blocks faithful recovery;
* total terminal thermalization is not faithful if there are two distinct
  memory states.

It does not claim that horizon evaporation implies recovery.
-/

import Mathlib

noncomputable section

namespace HorizonEschaton

/-! ## 1. Outcome labels -/

/--
The three eschatological horizon outcomes.

These are not metaphysical primitives. They are operational labels for
different algebraic outcomes.
-/
inductive HorizonOutcome where
  /-- Hidden memory becomes faithfully readable from exterior data. -/
  | revelation
  /-- Hidden memory distinctions dissolve into terminal equilibrium. -/
  | mahapralaya
  /-- Boundary changes, but neither recovery nor dissolution has been proved. -/
  | unresolved
deriving DecidableEq, Repr

/-! ## 2. Genesis: split/quench datum -/

/--
Genesis split datum.

This is the formal quench into distinction:

`Latent → Observable | Hidden`

with an optional boundary/horizon carrier.
-/
structure GenesisSplitDatum
    (Latent Observable Hidden Boundary : Type*) where
  /-- Observable/exterior readout. -/
  toObservable : Latent → Observable

  /-- Hidden/commutant memory projection. -/
  toHidden : Latent → Hidden

  /-- Horizon/boundary readout. -/
  boundaryOf : Latent → Boundary

  /--
  Explicit separation law for the full split/quench readout.

  The combined observable/hidden/boundary data determines the latent state.
  -/
  split_injective :
    Function.Injective (fun x => (toObservable x, toHidden x, boundaryOf x))

namespace GenesisSplitDatum

variable {Latent Observable Hidden Boundary : Type*}
variable (G : GenesisSplitDatum Latent Observable Hidden Boundary)

/-- If the full split readout agrees, the latent state agrees. -/
theorem latent_eq_of_split_eq
    {x y : Latent}
    (hobs : G.toObservable x = G.toObservable y)
    (hhidden : G.toHidden x = G.toHidden y)
    (hboundary : G.boundaryOf x = G.boundaryOf y) :
    x = y := by
  apply G.split_injective
  simp [hobs, hhidden, hboundary]

end GenesisSplitDatum

/-! ## 3. Hidden memory ledger -/

/--
A hidden-memory ledger indexed by events.

`observedDefect e` is what the exterior ledger sees.

`hiddenMemory e` is what the commutant/grade-two sector stores.
-/
structure HiddenMemoryLedger
    (Event Obs Memory : Type*) where
  observedDefect : Event → Obs
  hiddenMemory : Event → Memory

namespace HiddenMemoryLedger

variable {Event Obs Memory : Type*}
variable (L : HiddenMemoryLedger Event Obs Memory)

/--
Exterior observations separate hidden memory when distinct hidden memories
always imply distinct observed defects.
-/
def ExteriorSeparatesHidden : Prop :=
  ∀ e₁ e₂ : Event,
    L.hiddenMemory e₁ ≠ L.hiddenMemory e₂ →
      L.observedDefect e₁ ≠ L.observedDefect e₂

end HiddenMemoryLedger

/-! ## 4. Horizon evaporation datum -/

/--
Horizon evaporation datum.

Evaporation only records boundary evolution. It does not by itself decide
whether hidden memory is recovered, lost, or terminally dissolved.
-/
structure HorizonEvaporationDatum
    (Time Entropy : Type*) where
  /-- Horizon entropy/area/readout over time. -/
  horizonEntropy : Time → Entropy

namespace HorizonEvaporationDatum

variable {Time Entropy : Type*}
variable (E : HorizonEvaporationDatum Time Entropy)

/-- Equal times have equal horizon entropy readout. -/
theorem horizonEntropy_eq_of_time_eq
    {t₁ t₂ : Time}
    (ht : t₁ = t₂) :
    E.horizonEntropy t₁ = E.horizonEntropy t₂ := by
  simp [ht]

end HorizonEvaporationDatum

/-! ## 5. Revelation: faithful recovery -/

/--
Revelation recovery datum.

Hidden memory is faithfully unveiled if it can be reconstructed from exterior
observed-defect data.
-/
structure RevelationRecoveryDatum
    {Event Obs Memory : Type*}
    (L : HiddenMemoryLedger Event Obs Memory) where

  /-- Exterior decoding map. -/
  exteriorDecode : Obs → Memory

  /--
  Faithful recovery law:

  exterior data recovers the exact hidden memory for each event.
  -/
  faithful_recovery :
    ∀ e : Event,
      exteriorDecode (L.observedDefect e) =
        L.hiddenMemory e

namespace RevelationRecoveryDatum

variable {Event Obs Memory : Type*}
variable {L : HiddenMemoryLedger Event Obs Memory}
variable (R : RevelationRecoveryDatum L)

/--
If two events have the same exterior observation, a faithful recovery datum
forces their hidden memories to be equal.
-/
theorem hidden_eq_of_observed_eq
    (R : RevelationRecoveryDatum L)
    {e₁ e₂ : Event}
    (hobs : L.observedDefect e₁ = L.observedDefect e₂) :
    L.hiddenMemory e₁ = L.hiddenMemory e₂ := by
  exact
    (RevelationRecoveryDatum.faithful_recovery R e₁).symm.trans
      ((congrArg (RevelationRecoveryDatum.exteriorDecode R) hobs).trans
        (RevelationRecoveryDatum.faithful_recovery R e₂))

/--
Faithful recovery implies exterior observations separate hidden memory.
-/
theorem exterior_separates_hidden
    (R : RevelationRecoveryDatum L) :
    L.ExteriorSeparatesHidden := by
  intro e₁ e₂ hhidden hobs
  exact hhidden (RevelationRecoveryDatum.hidden_eq_of_observed_eq R hobs)

/--
If two events have different hidden memories, their observed defects must
differ under faithful recovery.
-/
theorem observedDefect_ne_of_hiddenMemory_ne
    (R : RevelationRecoveryDatum L)
    {e₁ e₂ : Event}
    (hmem : L.hiddenMemory e₁ ≠ L.hiddenMemory e₂) :
    L.observedDefect e₁ ≠ L.observedDefect e₂ :=
  (RevelationRecoveryDatum.exterior_separates_hidden R) e₁ e₂ hmem

end RevelationRecoveryDatum

/-! ## 6. Constructive obstruction to Revelation -/

/--
A witness that exterior data has collapsed distinct hidden memories.

This is the precise obstruction to faithful Revelation-style recovery.
-/
structure ExteriorCollapseWitness
    {Event Obs Memory : Type*}
    (L : HiddenMemoryLedger Event Obs Memory) where
  e₁ : Event
  e₂ : Event

  /-- Exterior cannot distinguish these events. -/
  same_observed :
    L.observedDefect e₁ = L.observedDefect e₂

  /-- But hidden memory distinguishes them. -/
  distinct_hidden :
    L.hiddenMemory e₁ ≠ L.hiddenMemory e₂

namespace ExteriorCollapseWitness

variable {Event Obs Memory : Type*}
variable {L : HiddenMemoryLedger Event Obs Memory}
variable (W : ExteriorCollapseWitness L)

/--
Exterior collapse of distinct hidden memories blocks faithful recovery.
-/
theorem no_faithful_recovery
    (W : ExteriorCollapseWitness L) :
    ¬ Nonempty (RevelationRecoveryDatum L) := by
  intro hR
  rcases hR with ⟨R⟩
  exact
    (ExteriorCollapseWitness.distinct_hidden W)
      (RevelationRecoveryDatum.hidden_eq_of_observed_eq R
        (ExteriorCollapseWitness.same_observed W))

end ExteriorCollapseWitness

/--
Evaporation plus an exterior-collapse witness does not yield Revelation.

This is the honest replacement for the invalid slogan
“evaporation does not imply recovery” as a bare theorem.
-/
structure EvaporationWithoutRecoveryWitness
    (Time Entropy Event Obs Memory : Type*) where
  evaporation :
    HorizonEvaporationDatum Time Entropy

  ledger :
    HiddenMemoryLedger Event Obs Memory

  collapse :
    ExteriorCollapseWitness ledger

namespace EvaporationWithoutRecoveryWitness

variable {Time Entropy Event Obs Memory : Type*}
variable (W :
  EvaporationWithoutRecoveryWitness Time Entropy Event Obs Memory)

/--
Given a concrete exterior-collapse witness, there is no faithful recovery datum
for the ledger.
-/
theorem no_faithful_recovery :
    ¬ Nonempty (RevelationRecoveryDatum W.ledger) :=
  ExteriorCollapseWitness.no_faithful_recovery W.collapse

end EvaporationWithoutRecoveryWitness

/-! ## 7. Mahapralaya: terminal dissolution -/

/--
Mahapralaya dissolution datum.

All hidden memory is mapped to a terminal thermalized state.

This is not recovery. It is de-individuation/collapse of distinction.
-/
structure PralayaDissolutionDatum
    (Memory Terminal : Type*) where
  /-- Thermalization/dissolution map. -/
  thermalize : Memory → Terminal

  /-- Terminal undifferentiated state. -/
  terminalState : Terminal

  /-- Every hidden memory thermalizes to the same terminal state. -/
  dissolution :
    ∀ m : Memory,
      thermalize m = terminalState

namespace PralayaDissolutionDatum

variable {Memory Terminal : Type*}
variable (P : PralayaDissolutionDatum Memory Terminal)

/--
All memories have the same terminal thermalized image.
-/
theorem thermalize_eq_thermalize
    (m₁ m₂ : Memory) :
    P.thermalize m₁ = P.thermalize m₂ := by
  rw [P.dissolution m₁, P.dissolution m₂]

/--
If two hidden memories are distinct, terminal dissolution is not injective.

So Mahapralaya is not faithful recovery when there is at least one genuine
hidden distinction.
-/
theorem not_injective_of_distinct_memories
    {m₁ m₂ : Memory}
    (hmem : m₁ ≠ m₂) :
    ¬ Function.Injective P.thermalize := by
  intro hinj
  apply hmem
  apply hinj
  exact P.thermalize_eq_thermalize m₁ m₂

/--
No decoder from the terminal image can recover two distinct memories after
total terminal dissolution.
-/
theorem no_two_point_recovery_after_dissolution
    {m₁ m₂ : Memory}
    (hne : m₁ ≠ m₂) :
    ¬ ∃ decode : Terminal → Memory,
      decode (P.thermalize m₁) = m₁ ∧
        decode (P.thermalize m₂) = m₂ := by
  intro h
  rcases h with ⟨decode, h₁, h₂⟩
  have hterm :
      P.thermalize m₁ = P.thermalize m₂ :=
    P.thermalize_eq_thermalize m₁ m₂
  have hdecode :
      decode (P.thermalize m₁) =
        decode (P.thermalize m₂) :=
    congrArg decode hterm
  have hm :
      m₁ = m₂ :=
    h₁.symm.trans (hdecode.trans h₂)
  exact hne hm

end PralayaDissolutionDatum

/-! ## 8. Revelation vs Mahapralaya boundary -/

/--
A ledger has a genuine hidden distinction when two events carry different
hidden memories.
-/
structure HiddenDistinctionWitness
    {Event Obs Memory : Type*}
    (L : HiddenMemoryLedger Event Obs Memory) where
  e₁ : Event
  e₂ : Event

  hidden_ne :
    L.hiddenMemory e₁ ≠ L.hiddenMemory e₂

namespace HiddenDistinctionWitness

variable {Event Obs Memory : Type*}
variable {L : HiddenMemoryLedger Event Obs Memory}
variable (W : HiddenDistinctionWitness L)

/--
If a Pralaya map dissolves all hidden memory to one terminal state, it cannot
be a faithful recovery of a genuine hidden distinction.
-/
theorem pralaya_not_faithful_recovery
    (W : HiddenDistinctionWitness L)
    {Terminal : Type*}
    (P : PralayaDissolutionDatum Memory Terminal) :
    ¬ Function.Injective P.thermalize :=
  P.not_injective_of_distinct_memories (HiddenDistinctionWitness.hidden_ne W)

end HiddenDistinctionWitness

/-! ## 9. Outcome witness package -/

/--
Operational eschaton package.

Evaporation is separated from the actual outcome. The outcome is determined
only after recovery/dissolution/unresolved witnesses are supplied.
-/
structure HorizonEschatonDatum
    (Time Entropy Event Obs Memory Terminal : Type*) where

  evaporation :
    HorizonEvaporationDatum Time Entropy

  ledger :
    HiddenMemoryLedger Event Obs Memory

  outcome :
    HorizonOutcome

  /-- Optional revelation witness. -/
  revelation :
    Option (RevelationRecoveryDatum ledger)

  /-- Optional Mahapralaya dissolution witness. -/
  pralaya :
    Option (PralayaDissolutionDatum Memory Terminal)

namespace HorizonEschatonDatum

variable {Time Entropy Event Obs Memory Terminal : Type*}
variable (E :
  HorizonEschatonDatum Time Entropy Event Obs Memory Terminal)

/--
If a revelation witness is present, hidden memory is externally decoded.
-/
theorem revelation_recovers
    (R : RevelationRecoveryDatum E.ledger)
    (e : Event) :
    R.exteriorDecode (E.ledger.observedDefect e) =
      E.ledger.hiddenMemory e :=
  R.faithful_recovery e

/--
If a Pralaya witness is present, all hidden memory has the same terminal image.
-/
theorem pralaya_collapses
    (P : PralayaDissolutionDatum Memory Terminal)
    (m₁ m₂ : Memory) :
    P.thermalize m₁ = P.thermalize m₂ :=
  P.thermalize_eq_thermalize m₁ m₂

end HorizonEschatonDatum

/-! ## 10. Terminal memory retention versus computational reset -/

/--
Terminal holographic memory retention.

The terminal readout still separates the original memory classes. This is the
Revelation-compatible case: the horizon may have changed or disappeared, but a
faithful terminal invariant remains.
-/
structure HolographicMemoryRetention
    (State Memory Readout : Type*) where
  /-- Terminalization/equilibration map on states. -/
  terminalize : State → State

  /-- Hidden memory readout before terminalization. -/
  memoryOf : State → Memory

  /-- Terminal/exterior invariant readout. -/
  readout : State → Readout

  /-- Terminal readout still separates memory classes. -/
  faithful_terminal_readout :
    ∀ x y : State,
      readout (terminalize x) = readout (terminalize y) →
        memoryOf x = memoryOf y

namespace HolographicMemoryRetention

variable {State Memory Readout : Type*}
variable (H : HolographicMemoryRetention State Memory Readout)

/--
Re-export of faithful terminal memory retention.
-/
theorem memory_eq_of_terminal_readout_eq
    {x y : State}
    (hread :
      H.readout (H.terminalize x) =
        H.readout (H.terminalize y)) :
    H.memoryOf x = H.memoryOf y :=
  H.faithful_terminal_readout x y hread

end HolographicMemoryRetention

/--
Mahapralaya/reset datum with terminal readout collapse.

All terminal readouts collapse to one value even though the pre-collapse memory
ledger contains at least two distinct memories.
-/
structure MahapralayaResetDatum
    (State Memory Readout : Type*) where
  /-- Terminalization/equilibration map on states. -/
  terminalize : State → State

  /-- Hidden memory readout before terminalization. -/
  memoryOf : State → Memory

  /-- Terminal/exterior readout. -/
  readout : State → Readout

  /-- The unique terminal readout. -/
  terminalReadout : Readout

  /-- Every state has the same terminal readout after terminalization. -/
  terminal_readout_collapse :
    ∀ x : State,
      readout (terminalize x) = terminalReadout

  /-- There were genuinely distinct memories before collapse. -/
  nontrivial_memory :
    ∃ x y : State,
      memoryOf x ≠ memoryOf y

namespace MahapralayaResetDatum

variable {State Memory Readout : Type*}
variable (R : MahapralayaResetDatum State Memory Readout)

/--
Any two terminalized states have the same terminal readout.
-/
theorem terminal_readout_eq
    (x y : State) :
    R.readout (R.terminalize x) =
      R.readout (R.terminalize y) := by
  rw [R.terminal_readout_collapse x, R.terminal_readout_collapse y]

/--
Terminal readout collapse forbids faithful memory retention.

This is the formal distinction between a reset and holographic memory:
if all terminal readouts are identical while pre-collapse memories differ, then
the terminal readout cannot separate memory classes.
-/
theorem terminal_collapse_not_faithful :
    ¬ ∀ x y : State,
      R.readout (R.terminalize x) = R.readout (R.terminalize y) →
        R.memoryOf x = R.memoryOf y := by
  intro hfaithful
  rcases R.nontrivial_memory with ⟨x, y, hxy⟩
  have hread :
      R.readout (R.terminalize x) =
        R.readout (R.terminalize y) :=
    R.terminal_readout_eq x y
  exact hxy (hfaithful x y hread)

end MahapralayaResetDatum

/--
Retention datum at the memory/readout level.

This records a faithful terminal invariant directly on memories.
-/
structure HolographicRetentionDatum
    (Memory Readout : Type*) where
  /-- Terminal encoding/readout of memory. -/
  encode : Memory → Readout

  /-- The terminal invariant separates memory states. -/
  faithful : Function.Injective encode

/--
Reset datum at the memory/readout level.

The terminal encoding collapses all memories to one readout while the memory
space contains a nontrivial distinction.
-/
structure ComputationalResetDatum
    (Memory Readout : Type*) where
  /-- Terminal encoding/readout of memory. -/
  encode : Memory → Readout

  /-- The unique terminal readout. -/
  terminalReadout : Readout

  /-- All memories share the same terminal readout. -/
  collapse :
    ∀ m : Memory,
      encode m = terminalReadout

  /-- There were genuinely distinct memories before collapse. -/
  nontrivialMemory :
    ∃ m₁ m₂ : Memory,
      m₁ ≠ m₂

namespace ComputationalResetDatum

variable {Memory Readout : Type*}
variable (R : ComputationalResetDatum Memory Readout)

/--
Any two memories have the same terminal readout under reset collapse.
-/
theorem encode_eq_encode
    (m₁ m₂ : Memory) :
    R.encode m₁ = R.encode m₂ := by
  rw [R.collapse m₁, R.collapse m₂]

/--
Many-to-one terminal readout contradicts faithful holographic retention.
-/
theorem collapse_forbids_faithful_retention :
    ¬ Function.Injective R.encode := by
  intro hinj
  rcases R.nontrivialMemory with ⟨m₁, m₂, hneq⟩
  exact hneq (hinj (R.encode_eq_encode m₁ m₂))

end ComputationalResetDatum

/--
A classified horizon process.

This stores a label and a proof-carrying explanation law. Concrete models
should use the more specific bridge structures above.
-/
structure HorizonProcessClassification where
  outcome : HorizonOutcome

namespace HorizonProcessClassification

variable (C : HorizonProcessClassification)

/-- Any classified process falls into exactly one of the three outcome branches. -/
theorem exhaustive :
    C.outcome = HorizonOutcome.revelation ∨
      C.outcome = HorizonOutcome.mahapralaya ∨
      C.outcome = HorizonOutcome.unresolved := by
  cases C.outcome <;> simp

end HorizonProcessClassification

/-! ## 11. Owner targets -/

/--
Owner target for Genesis/quench split readout.
-/
def GenesisQuenchOwnerTarget
    (Latent Observable Hidden Boundary : Type*) : Prop :=
  ∀ G : GenesisSplitDatum Latent Observable Hidden Boundary,
    ∀ x y : Latent,
      G.toObservable x = G.toObservable y →
      G.toHidden x = G.toHidden y →
      G.boundaryOf x = G.boundaryOf y →
        x = y

/-- A supplied Genesis split datum separates latent states by full readout. -/
theorem genesisQuenchOwnerTarget
    (Latent Observable Hidden Boundary : Type*) :
    GenesisQuenchOwnerTarget Latent Observable Hidden Boundary := by
  intro G x y hobs hhidden hboundary
  exact G.latent_eq_of_split_eq hobs hhidden hboundary

/--
Owner target for Revelation/recovery readout.
-/
def RevelationRecoveryOwnerTarget
    (Event Obs Memory : Type*) : Prop :=
  ∀ L : HiddenMemoryLedger Event Obs Memory,
    ∀ R : RevelationRecoveryDatum L,
      L.ExteriorSeparatesHidden ∧
        (∀ e : Event,
          R.exteriorDecode (L.observedDefect e) = L.hiddenMemory e)

/-- A supplied Revelation datum separates hidden memory through exterior data. -/
theorem revelationRecoveryOwnerTarget
    (Event Obs Memory : Type*) :
    RevelationRecoveryOwnerTarget Event Obs Memory := by
  intro L R
  exact ⟨R.exterior_separates_hidden, fun e => R.faithful_recovery e⟩

/--
Owner target for Pralaya/dissolution readout.
-/
def PralayaDissolutionOwnerTarget
    (Memory Thermal : Type*) : Prop :=
  ∀ P : PralayaDissolutionDatum Memory Thermal,
    ∀ m₁ m₂ : Memory,
      P.thermalize m₁ = P.thermalize m₂

/-- A supplied Pralaya datum collapses all memories to the same terminal image. -/
theorem pralayaDissolutionOwnerTarget
    (Memory Thermal : Type*) :
    PralayaDissolutionOwnerTarget Memory Thermal := by
  intro P m₁ m₂
  exact P.thermalize_eq_thermalize m₁ m₂

/--
Owner target for evaporation plus exterior-collapse obstruction.
-/
def EvaporationWithoutRecoveryOwnerTarget
    (Time Entropy Event Obs Memory : Type*) : Prop :=
  ∀ W : EvaporationWithoutRecoveryWitness Time Entropy Event Obs Memory,
    ¬ Nonempty (RevelationRecoveryDatum W.ledger)

/-- Exterior collapse blocks faithful Revelation recovery for the witness ledger. -/
theorem evaporationWithoutRecoveryOwnerTarget
    (Time Entropy Event Obs Memory : Type*) :
    EvaporationWithoutRecoveryOwnerTarget Time Entropy Event Obs Memory := by
  intro W
  exact W.no_faithful_recovery

/--
Owner target for operational eschaton branch readout.
-/
def HorizonEschatonOwnerTarget
    (Time Entropy Event Obs Memory Terminal : Type*) : Prop :=
  ∀ E : HorizonEschatonDatum Time Entropy Event Obs Memory Terminal,
    (∀ R : RevelationRecoveryDatum E.ledger,
      ∀ e : Event,
        R.exteriorDecode (E.ledger.observedDefect e) =
          E.ledger.hiddenMemory e) ∧
    (∀ P : PralayaDissolutionDatum Memory Terminal,
      ∀ m₁ m₂ : Memory,
        P.thermalize m₁ = P.thermalize m₂)

/-- A supplied eschaton datum exposes the Revelation and Pralaya branch laws. -/
theorem horizonEschatonOwnerTarget
    (Time Entropy Event Obs Memory Terminal : Type*) :
    HorizonEschatonOwnerTarget Time Entropy Event Obs Memory Terminal := by
  intro E
  exact ⟨
    (fun R e => E.revelation_recovers R e),
    (fun P m₁ m₂ =>
      HorizonEschatonDatum.pralaya_collapses
        (P := P) (m₁ := m₁) (m₂ := m₂))⟩

/--
Owner target for holographic terminal memory retention.
-/
def HolographicMemoryRetentionOwnerTarget
    (State Memory Readout : Type*) : Prop :=
  ∀ H : HolographicMemoryRetention State Memory Readout,
    ∀ x y : State,
      H.readout (H.terminalize x) =
        H.readout (H.terminalize y) →
          H.memoryOf x = H.memoryOf y

/-- A supplied terminal-retention datum faithfully reads memory from terminal data. -/
theorem holographicMemoryRetentionOwnerTarget
    (State Memory Readout : Type*) :
    HolographicMemoryRetentionOwnerTarget State Memory Readout := by
  intro H x y hread
  exact H.memory_eq_of_terminal_readout_eq hread

/--
Owner target for Mahapralaya/reset obstruction.
-/
def MahapralayaResetOwnerTarget
    (State Memory Readout : Type*) : Prop :=
  ∀ R : MahapralayaResetDatum State Memory Readout,
    (∀ x y : State,
      R.readout (R.terminalize x) =
        R.readout (R.terminalize y)) ∧
    ¬ ∀ x y : State,
      R.readout (R.terminalize x) =
        R.readout (R.terminalize y) →
          R.memoryOf x = R.memoryOf y

/-- A supplied reset datum collapses terminal readout and forbids faithful retention. -/
theorem mahapralayaResetOwnerTarget
    (State Memory Readout : Type*) :
    MahapralayaResetOwnerTarget State Memory Readout := by
  intro R
  exact ⟨
    (fun x y => R.terminal_readout_eq x y),
    R.terminal_collapse_not_faithful⟩

/--
Owner target for memory-level holographic retention data.
-/
def HolographicRetentionOwnerTarget
    (Memory Readout : Type*) : Prop :=
  ∀ H : HolographicRetentionDatum Memory Readout,
    Function.Injective H.encode

/-- A supplied memory-level retention datum is exactly an injective encoding. -/
theorem holographicRetentionOwnerTarget
    (Memory Readout : Type*) :
    HolographicRetentionOwnerTarget Memory Readout := by
  intro H
  exact H.faithful

/--
Owner target for memory-level computational reset data.
-/
def ComputationalResetOwnerTarget
    (Memory Readout : Type*) : Prop :=
  ∀ R : ComputationalResetDatum Memory Readout,
    (∀ m₁ m₂ : Memory, R.encode m₁ = R.encode m₂) ∧
      ¬ Function.Injective R.encode

/-- A supplied computational reset collapses encoding and cannot be faithful. -/
theorem computationalResetOwnerTarget
    (Memory Readout : Type*) :
    ComputationalResetOwnerTarget Memory Readout := by
  intro R
  exact ⟨
    (fun m₁ m₂ => R.encode_eq_encode m₁ m₂),
    R.collapse_forbids_faithful_retention⟩

end HorizonEschaton
