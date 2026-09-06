branch.

For a metal mirror, `actual` is the lossy reflected branch and `ideal` is the
lossless/unitary reference reflection.
-/
structure OpenSystemChannel
    (State : Type*) [AddCommGroup State] [Module ℝ State] where
  /-- Observed open-system branch. -/
  actual : State →ₗ[ℝ] State

  /-- Ideal closed/lossless reference branch. -/
  ideal : State →ₗ[ℝ] State

  /-- Domain on which the channel/readouts are intended to apply. -/
  regularDomain : Set State

  actual_preserves_regular :
    ∀ x : State, x ∈ regularDomain → actual x ∈ regularDomain

  ideal_preserves_regular :
    ∀ x : State, x ∈ regularDomain → ideal x ∈ regularDomain

/-! ## 3. Stinespring/Tomita dilation datum -/

/--
A Stinespring/Tomita-style dilation.

`Joint` is the enlarged system + environment carrier.

`Env` is the hidden environment/commutant carrier.

The key law is:

`ideal x = actual x + mirrorLeak(hiddenLeak x)`.

Thus the observed deficit between ideal and actual flow is represented as a
mirrored leak from the hidden sector.
-/
structure StinespringDilation
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : OpenSystemChannel State) where

  /-- Embed observed system states into the enlarged carrier. -/
  embedSystem : State →ₗ[ℝ] Joint

  /-- Closed evolution on the enlarged carrier. -/
  jointEvolution : Joint →ₗ[ℝ] Joint

  /-- Reduction back to the observed system branch. -/
  reduceSystem : Joint →ₗ[ℝ] State

  /-- Hidden/environment readout from the enlarged carrier. -/
  hiddenLeak : Joint →ₗ[ℝ] Env

  /-- Mirror/environment contribution back into system-comparison units. -/
  mirrorLeak : Env →ₗ[ℝ] State

  /-- Actual observed channel is the reduced joint evolution. -/
  actual_eq_reduced :
    ∀ x : State,
      C.actual x =
        reduceSystem (jointEvolution (embedSystem x))

  /--
  Conservation of distinguishability/accounting:

  the ideal reference state decomposes into the actual observed branch plus the
  mirrored hidden/environment contribution.
  -/
  conservation :
    ∀ x : State,
      C.ideal x =
        C.actual x +
          mirrorLeak (hiddenLeak (jointEvolution (embedSystem x)))

namespace StinespringDilation

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}

variable (D : StinespringDilation State Env Joint C)

/-- Hidden environment leak after joint evolution. -/
def hiddenComponent
    (x : State) : Env :=
  D.hiddenLeak (D.jointEvolution (D.embedSystem x))

/-- Mirrored hidden contribution in system units. -/
def mirroredHiddenComponent
    (x : State) : State :=
  D.mirrorLeak (D.hiddenComponent x)

/--
The ideal-minus-actual deficit is exactly the mirrored hidden component.