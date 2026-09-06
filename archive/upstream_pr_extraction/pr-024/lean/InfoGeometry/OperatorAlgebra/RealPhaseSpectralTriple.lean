/-
InfoGeometry/OperatorAlgebra/RealPhaseSpectralTriple.lean

Real phase-compatible spectral triple sockets.

This module keeps the strict separation:

* `K` is the Hestenes phase axis / real complex structure;
* `J` is a real structure represented real-linearly;
* `J` reverses phase rather than being identified with `K`.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.OperatorAlgebra.RenormalizedTrace

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple

open scoped ENNReal

/-! ## 1. Real bounded operator notation -/

/-- Bounded real-linear endomorphisms. -/
abbrev RealEnd
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-! ## 2. Phase preservation and reversal -/

/-- A real-linear operator preserves phase axes when it intertwines them. -/
def PhasePreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (K₁ : RealEnd H₁)
    (K₂ : RealEnd H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp K₁ = K₂.comp F

/-- A real-linear operator reverses phase axes when it anticommutes with them. -/
def PhaseReversing
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (K₁ : RealEnd H₁)
    (K₂ : RealEnd H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp K₁ = -(K₂.comp F)

/-! ## 3. Phase axis and real structure -/

/--
Hestenes phase axis.

This is the real-linear complex structure. It is not the Connes/Tomita real
structure `J`.
-/
structure PhaseAxis
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  K : RealEnd H
  K_sq :
    K.comp K = -1

/--
Real structure represented real-linearly.

Its anti-linearity relative to the phase axis is encoded by phase reversal:
`J K = -K J`.
-/
structure PhaseRealStructure
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H) where
  J : RealEnd H
  J_square : J.comp J = 1
  J_reverses_phase :
    PhaseReversing K.K K.K J

namespace PhaseRealStructure

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    (J : PhaseRealStructure H K)

/-- Point-free form of `J K = -K J`. -/
theorem reverses_phase :
    J.J.comp K.K = -(K.K.comp J.J) :=
  J.J_reverses_phase

end PhaseRealStructure

/-! ## 4. Grading, Dirac generator, and representation -/

/-- A chiral grading compatible with the phase axis. -/
structure ChiralGrading
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H) where
  chi : RealEnd H
  chi_square : chi.comp chi = 1
  chi_phase_linear : PhasePreserving K.K K.K chi

/-- Bounded spectral/Dirac generator with explicit model obligations. -/
structure SpectralGenerator
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  D : RealEnd H
  selfAdjointOrKreinSelfAdjoint : Prop
  summabilityOrCompactResolvent : Prop

/-- Commutator of bounded real endomorphisms. -/
def commutator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S T : RealEnd H) : RealEnd H :=
  S.comp T - T.comp S

namespace SpectralGenerator

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : SpectralGenerator H)

@[simp]
theorem comp_id :
    D.D.comp (ContinuousLinearMap.id ℝ H) = D.D := by
  ext x
  rfl

@[simp]
theorem id_comp :
    (ContinuousLinearMap.id ℝ H).comp D.D = D.D := by
  ext x
  rfl

@[simp]
theorem commutator_self :
    commutator D.D D.D = 0 := by
  ext x
  simp [commutator]

end SpectralGenerator

/-- A represented real operator algebra. -/
structure RepresentedAlgebra
    (A H : Type*) [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  rep : A →+* RealEnd H

/-- Order-one condition, kept as a witness at the abstract layer. -/
def OrderOneCondition
    {A H : Type*} [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : RepresentedAlgebra A H)
    (D : SpectralGenerator H) : Prop :=
  ∀ a b : A,
    (commutator D.D (ρ.rep a)).comp (ρ.rep b) =
      (ρ.rep b).comp (commutator D.D (ρ.rep a))

/-- Spectral Lipschitz seminorm candidate `a ↦ ‖[D, ρ(a)]‖`. -/
def lipschitzSeminorm
    {A H : Type*} [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : RepresentedAlgebra A H)
    (D : SpectralGenerator H)
    (a : A) : ℝ :=
  ‖commutator D.D (ρ.rep a)‖

theorem lipschitzSeminorm_nonneg
    {A H : Type*} [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : RepresentedAlgebra A H)
    (D : SpectralGenerator H)
    (a : A) :
    0 ≤ lipschitzSeminorm ρ D a :=
  norm_nonneg _

/-! ## 5. Phase-real spectral triple socket -/

/--
Real, phase-compatible spectral triple socket.

The `order_one` field is supplied abstractly and should be proved in concrete
representation modules.
-/
structure PhaseRealSpectralTriple
    (A H : Type*) [Ring A] [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  phaseAxis : PhaseAxis H
  realStructure : PhaseRealStructure H phaseAxis
  grading : ChiralGrading H phaseAxis
  spectralGenerator : SpectralGenerator H
  representedAlgebra : RepresentedAlgebra A H
  order_one : OrderOneCondition representedAlgebra spectralGenerator
  traceBackend : Option (TraceDatum (RealEnd H))
  modularWeightBackend : Option (ModularWeightDatum (RealEnd H))
  renormalizedBackend : Option (RenormalizedTraceBackend (RealEnd H))

namespace PhaseRealSpectralTriple

variable
    {A H : Type*} [Ring A] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : PhaseRealSpectralTriple A H)

/-- The spectral triple's Lipschitz seminorm. -/
def lipschitz (a : A) : ℝ :=
  lipschitzSeminorm T.representedAlgebra T.spectralGenerator a

theorem lipschitz_nonneg (a : A) :
    0 ≤ T.lipschitz a :=
  lipschitzSeminorm_nonneg T.representedAlgebra T.spectralGenerator a

end PhaseRealSpectralTriple

end InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple
