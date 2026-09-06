import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RefinementLoopShadow

A theorem-facing shadow for iterative refinement loops.

This file does not identify latent internal recurrence with authority. It only
packages the narrow structure that can be reused honestly in the repo:

- an iterative update lane,
- an explicit stability witness,
- an explicit halting gate,
- and a boundary-separated readout.
-/

namespace InfoGeometry.Canonical.RefinementLoopShadow

universe u v

/-- The bare iterative refinement packet. -/
@[rep_depth transport]
structure RefinementLoop (State Readout : Type u) where
  step : State → State
  readout : State → Readout
  halted : State → Prop

namespace RefinementLoop

variable {State Readout : Type u}
variable (L : RefinementLoop State Readout)

@[rep_depth transport]
def iterate (L : RefinementLoop State Readout) : Nat → State → State
  | 0, s => s
  | n + 1, s => L.step (iterate L n s)

@[rep_depth transport]
def readoutAfter (n : Nat) (s : State) : Readout :=
  L.readout (iterate L n s)

@[rep_depth transport]
def haltedAfter (n : Nat) (s : State) : Prop :=
  L.halted (iterate L n s)

@[rep_depth transport]
theorem iterate_succ (n : Nat) (s : State) :
    iterate L (n + 1) s = L.step (iterate L n s) := rfl

end RefinementLoop

/--
A proof-carrying stability interface.

The point is not to force one numerical notion of stability, but to make the
control law explicit and theorem-facing.
-/
@[rep_depth transport]
structure StabilityWitness (State : Type u) where
  Stable : State → State → Prop
  step_preserves : ∀ {f : State → State} {s t : State},
    Stable s t → Stable (f s) (f t)

/--
A halting gate states that once the loop halts, another refinement step does not
change the readout boundary value.
-/
@[rep_depth transport]
structure HaltingGate (State Readout : Type u) where
  boundaryReadout : State → Readout
  boundary_of_halted : ∀ {step : State → State} {halted : State → Prop} {s : State},
    halted s → boundaryReadout (step s) = boundaryReadout s

/--
The full theorem-facing packet: refinement, stability, and halting/readout are
kept explicit and separated.
-/
@[rep_depth transport]
structure RefinementLoopShadow (State Readout : Type u) where
  loop : RefinementLoop State Readout
  stability : StabilityWitness State
  halting : HaltingGate State Readout
  authorityReadout : Readout → Prop

namespace RefinementLoopShadow

variable {State Readout : Type u}
variable (S : RefinementLoopShadow State Readout)

@[rep_depth transport]
def iterate (n : Nat) (s : State) : State :=
  RefinementLoop.iterate S.loop n s

@[rep_depth transport]
def boundaryReadoutAfter (n : Nat) (s : State) : Readout :=
  S.halting.boundaryReadout (iterate S n s)

/-- If the loop is halted at stage `n`, the next step preserves boundary readout. -/
@[rep_depth transport]
theorem boundaryReadout_constant_after_halt
    (n : Nat) (s : State)
    (h : S.loop.halted (iterate S n s)) :
    boundaryReadoutAfter S (n + 1) s = boundaryReadoutAfter S n s := by
  simp [boundaryReadoutAfter, iterate, RefinementLoop.iterate]
  exact S.halting.boundary_of_halted h

/--
Boundary authority is asserted only on readout, not on the internal iterate.
-/
@[rep_depth transport]
def HaltedReadoutIsAuthoritative (n : Nat) (s : State) : Prop :=
  S.loop.halted (iterate S n s) →
    S.authorityReadout (S.halting.boundaryReadout (iterate S n s))

end RefinementLoopShadow

end InfoGeometry.Canonical.RefinementLoopShadow
