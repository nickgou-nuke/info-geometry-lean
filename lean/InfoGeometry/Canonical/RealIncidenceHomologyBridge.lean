import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.HestenesPhaseSemilinear
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RealIncidenceHomologyBridge

Theorem-safe real homology/cohomology socket for incidence and wire complexes.

This file records the real Hestenes--Krein translation:

* homology is closed real incidence data modulo supplied real boundaries;
* cohomology is real readout data modulo supplied coboundaries;
* phase-sensitive cochains are represented by compatibility with an internal
  real phase axis `K`, not by scalar-complex coefficients;
* chiral Dirac/Hodge representatives are read through the existing
  `ChiralHodgeDecomposition` owner surface.

It does not construct quotient spaces, prove a full Hodge theorem, or assert
that a Dirac lane is automatically a nilpotent chain differential. Those remain
explicit witness/calibration layers.
-/

namespace InfoGeometry.Canonical.RealIncidenceHomologyBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.ChiralHodgeDecomposition
open InfoGeometry.Canonical.HestenesPhaseSemilinear

/--
A real chain-complex socket.

`C n` is the degree-`n` chain carrier, `boundary n : C (n+1) -> C n` is the
real boundary map, and `boundary_boundary_zero` is the supplied chain-complex
law `∂ ∂ = 0`.
-/
@[rep_depth transport]
structure RealChainComplex where
  C : ℕ → Type u
  zero : ∀ n, C n
  boundary : ∀ n, C (n + 1) → C n
  boundary_boundary_zero :
    ∀ n (x : C (n + 2)), boundary n (boundary (n + 1) x) = zero n

namespace RealChainComplex

variable (K : RealChainComplex)

/-- A degree-`n+1` cycle is killed by the degree-`n` boundary map. -/
@[rep_depth transport]
def IsCycleAtSucc (n : ℕ) (x : K.C (n + 1)) : Prop :=
  K.boundary n x = K.zero n

/-- A degree-`n` boundary is produced from a degree-`n+1` chain. -/
@[rep_depth transport]
def IsBoundary (n : ℕ) (x : K.C n) : Prop :=
  ∃ y : K.C (n + 1), K.boundary n y = x

/-- Readback of the supplied nilpotence law `∂ ∂ = 0`. -/
@[rep_depth transport]
theorem boundary_boundary_zero_readback
    (n : ℕ) (x : K.C (n + 2)) :
    K.boundary n (K.boundary (n + 1) x) = K.zero n :=
  K.boundary_boundary_zero n x

/-- Every boundary of a higher chain is a cycle, by `∂ ∂ = 0`. -/
@[rep_depth transport]
theorem boundary_is_cycle
    (n : ℕ) (x : K.C (n + 2)) :
    K.IsCycleAtSucc n (K.boundary (n + 1) x) :=
  K.boundary_boundary_zero n x

end RealChainComplex

/--
A real cochain-complex socket.

This is the dual readout lane. `coboundary n` sends degree-`n` cochains to
degree-`n+1` cochains, and `coboundary_coboundary_zero` supplies `d d = 0`.
-/
@[rep_depth transport]
structure RealCochainComplex where
  C : ℕ → Type u
  V : Type v
  zeroV : V
  coboundary : ∀ n, (C n → V) → (C (n + 1) → V)
  coboundary_coboundary_zero :
    ∀ n (α : C n → V), coboundary (n + 1) (coboundary n α) = fun _ => zeroV

namespace RealCochainComplex

variable (K : RealCochainComplex)

/-- A cocycle is a cochain killed by the next coboundary. -/
@[rep_depth transport]
def IsCocycle (n : ℕ) (α : K.C n → K.V) : Prop :=
  K.coboundary n α = fun _ => K.zeroV

/-- A successor-degree coboundary is produced by a lower-degree cochain. -/
@[rep_depth transport]
def IsCoboundaryAtSucc (n : ℕ) (α : K.C (n + 1) → K.V) : Prop :=
  ∃ β : K.C n → K.V, K.coboundary n β = α

/-- Readback of the supplied cochain nilpotence law `d d = 0`. -/
@[rep_depth transport]
theorem coboundary_coboundary_zero_readback
    (n : ℕ) (α : K.C n → K.V) :
    K.coboundary (n + 1) (K.coboundary n α) = fun _ => K.zeroV :=
  K.coboundary_coboundary_zero n α

/-- Every coboundary is a cocycle, by `d d = 0`. -/
@[rep_depth transport]
theorem coboundary_is_cocycle
    (n : ℕ) (α : K.C n → K.V) :
    K.IsCocycle (n + 1) (K.coboundary n α) :=
  K.coboundary_coboundary_zero n α

end RealCochainComplex

/--
A real coefficient carrier with an internal Hestenes phase axis.

This is the coefficient-level replacement for scalar-complex coefficients:
phase is represented by a real operator `phase` with square `-1`.
-/
@[rep_depth krein]
structure HestenesCoefficientModule where
  V : Type u
  [neg : Neg V]
  phase : V → V
  phase_sq_neg : ∀ v : V, phase (phase v) = -v

attribute [instance] HestenesCoefficientModule.neg

/--
A cochain readout is Hestenes-linear when it intertwines the source phase and
coefficient phase.
-/
@[rep_depth krein]
def IsHestenesLinearCochain
    {C V : Type u}
    (sourcePhase : C → C)
    (targetPhase : V → V)
    (α : C → V) : Prop :=
  ∀ x, α (sourcePhase x) = targetPhase (α x)

namespace IsHestenesLinearCochain

variable {C V : Type u}
variable (sourcePhase : C → C) (targetPhase : V → V) (α : C → V)

/-- Pointwise readback of Hestenes-linearity for cochains. -/
@[rep_depth krein]
theorem apply
    (hα : IsHestenesLinearCochain sourcePhase targetPhase α)
    (x : C) :
    α (sourcePhase x) = targetPhase (α x) :=
  hα x

end IsHestenesLinearCochain

section ChiralDirac

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Plus chiral cycles are killed by the outgoing `D⁺` arrow. -/
@[rep_depth krein]
def IsPlusChiralCycle (u : H₂) : Prop :=
  rootDiracPlus (E := E) u = 0

/-- Minus chiral cycles are killed by the outgoing `D⁻` arrow. -/
@[rep_depth krein]
def IsMinusChiralCycle (u : H₂) : Prop :=
  rootDiracMinus (E := E) u = 0

/-- Plus boundaries are produced by the incoming `D⁻` arrow. -/
@[rep_depth krein]
def IsPlusChiralBoundary (u : H₂) : Prop :=
  ∃ v : H₂, rootDiracMinus (E := E) v = u

/-- Minus boundaries are produced by the incoming `D⁺` arrow. -/
@[rep_depth krein]
def IsMinusChiralBoundary (u : H₂) : Prop :=
  ∃ v : H₂, rootDiracPlus (E := E) v = u

/-- Plus harmonic representatives are killed by `Δ₊ = D⁻D⁺`. -/
@[rep_depth krein]
def IsPlusChiralHarmonic (u : H₂) : Prop :=
  rootChiralLaplacianPlus (E := E) u = 0

/-- Minus harmonic representatives are killed by `Δ₋ = D⁺D⁻`. -/
@[rep_depth krein]
def IsMinusChiralHarmonic (u : H₂) : Prop :=
  rootChiralLaplacianMinus (E := E) u = 0

/-- Readback: the root odd Dirac lane splits into its two chiral arrows. -/
@[rep_depth krein]
theorem rootDirac_eq_chiral_arrows :
    rootDiracOddLane (E := E) = rootDiracPlus (E := E) + rootDiracMinus (E := E) :=
  rootDiracOddLane_eq_chiral_sum (E := E)

/-- Readback: the plus Hodge loop is the plus chiral projector. -/
@[rep_depth krein]
theorem plus_hodge_loop_eq_projector :
    rootChiralLaplacianPlus (E := E) = spectralChiralPlusProjector (E := E) :=
  rootChiralLaplacianPlus_eq_spectralChiralPlusProjector (E := E)

/-- Readback: the minus Hodge loop is the minus chiral projector. -/
@[rep_depth krein]
theorem minus_hodge_loop_eq_projector :
    rootChiralLaplacianMinus (E := E) = spectralChiralMinusProjector (E := E) :=
  rootChiralLaplacianMinus_eq_spectralChiralMinusProjector (E := E)

/-- Readback: `D²` is the sum of the two chiral Hodge loops. -/
@[rep_depth krein]
theorem rootDirac_sq_eq_hodge_loop_sum :
    (rootDiracOddLane (E := E)).comp (rootDiracOddLane (E := E))
      = rootChiralLaplacianPlus (E := E) + rootChiralLaplacianMinus (E := E) :=
  rootDiracOddLane_sq_eq_chiralLaplacian_sum (E := E)

/--
A nilpotent chiral complex witness.

Only with this witness should quotient-style chiral homology
`ker D± / im D∓` be interpreted as an actual chain-complex homology lane.
-/
@[rep_depth krein]
abbrev ChiralNilpotentComplexWitness : Prop :=
  (rootDiracPlus (E := E)).comp (rootDiracMinus (E := E)) = 0 ∧
    (rootDiracMinus (E := E)).comp (rootDiracPlus (E := E)) = 0

namespace ChiralNilpotentComplexWitness

variable (W : ChiralNilpotentComplexWitness (E := E))

/-- With a nilpotent-complex witness, plus boundaries are plus cycles. -/
@[rep_depth krein]
theorem plus_boundary_is_cycle
    (W : ChiralNilpotentComplexWitness (E := E))
    {u : H₂} (hu : IsPlusChiralBoundary (E := E) u) :
    IsPlusChiralCycle (E := E) u := by
  rcases hu with ⟨v, rfl⟩
  unfold IsPlusChiralCycle
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun F : EndH => F v) W.1

/-- With a nilpotent-complex witness, minus boundaries are minus cycles. -/
@[rep_depth krein]
theorem minus_boundary_is_cycle
    (W : ChiralNilpotentComplexWitness (E := E))
    {u : H₂} (hu : IsMinusChiralBoundary (E := E) u) :
    IsMinusChiralCycle (E := E) u := by
  rcases hu with ⟨v, rfl⟩
  unfold IsMinusChiralCycle
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun F : EndH => F v) W.2

end ChiralNilpotentComplexWitness

end ChiralDirac

end InfoGeometry.Canonical.RealIncidenceHomologyBridge
