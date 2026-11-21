/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum
import InfoGeometry.Canonical.ConnesSpectralTripleBridge
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Bounded real modular derivations and commutator Lipschitz seminorms

On the existing doubled real Hilbert carrier, the relative modular generator
`G = relativeModularKGenerator hMod` acts on observables by the already-owned
inner derivation `relativeModularDeriv hMod A = G * A - A * G`.

This module identifies that derivation with the repository's bounded
commutator-seminorm interface, proves its kernel and Lipschitz consequences,
and transports the existing obstruction to finite spectral distance. The
norm throughout is the positive Hilbert operator norm, not the indefinite
Krein pairing. No complex scalar, finite matrix carrier, unbounded Dirac
operator, compact-resolvent assertion, or manifold Killing field is added.

The term Killing refers here only to an observable in the kernel of the
relative modular derivation. The higher thermodynamic owner names precisely
this stationarity condition `IsPotentialKillingOperator`; this lower owner
does not import that owner's additional thermodynamic dependency graph.

Stationary observables are fixed at every time by the existing exponential
conjugation, with no self-adjointness or phase-linearity hypothesis needed.
Under the separate self-adjoint and phase-linear seed hypotheses, the state
transport is also an isometry of the positive Hilbert norm.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauKillingLipschitzBridge

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance

/-- The existing relative modular generator in the bounded commutator
interface. This structure asserts no analytic spectral-triple axioms. -/
def souriauSpectralData (hMod : EndH) : ConnesSpectral.SpectralTriple EndH where
  dirac := relativeModularKGenerator (E := E) hMod

/-- The two independently owned commutator constructions agree exactly. -/
@[simp] theorem commutator_eq_relativeModularDeriv (hMod A : EndH) :
    (souriauSpectralData hMod).commutator A =
      relativeModularDeriv (E := E) hMod A := rfl

/-- The Souriau commutator seminorm is the norm of the actual modular
derivation, rather than an independently supplied seminorm. -/
@[simp] theorem commutatorNorm_eq (hMod A : EndH) :
    (souriauSpectralData hMod).commutatorNorm A =
      ‖relativeModularDeriv (E := E) hMod A‖ := rfl

/-- Vanishing of the seminorm is exactly stationarity of the observable. -/
theorem commutatorNorm_eq_zero_iff_relativeModularDeriv_eq_zero (hMod A : EndH) :
    (souriauSpectralData hMod).commutatorNorm A = 0 ↔
      relativeModularDeriv (E := E) hMod A = 0 := by
  rw [commutatorNorm_eq]
  exact ContinuousLinearMap.opNorm_zero_iff (relativeModularDeriv (E := E) hMod A)

/-- The stationary observables are precisely the commutant of the existing
relative modular generator. -/
theorem relativeModularDeriv_eq_zero_iff_commute (hMod A : EndH) :
    relativeModularDeriv (E := E) hMod A = 0 ↔
      Commute (relativeModularKGenerator (E := E) hMod) A := by
  rw [← commutatorNorm_eq_zero_iff_relativeModularDeriv_eq_zero]
  exact (souriauSpectralData hMod).commutatorNorm_eq_zero_iff_commute A

section CompleteFlow

variable [CompleteSpace E]

/-- Infinitesimal stationarity fixes the observable under exact exponential
conjugation for every real time. -/
theorem expTransport_eq_self_of_relativeModularDeriv_eq_zero
    (hMod A : EndH) (t : ℝ)
    (hKernel : relativeModularDeriv (E := E) hMod A = 0) :
    expTransport (relativeModularKGenerator (E := E) hMod) A t = A := by
  exact expTransport_eq_self_of_commute
    (relativeModularKGenerator (E := E) hMod) A t
    ((relativeModularDeriv_eq_zero_iff_commute hMod A).1 hKernel).symm

/-- An observable is stationary exactly when the full exponential
conjugation fixes it at every real time. The converse differentiates the
actual transport at zero. -/
theorem relativeModularDeriv_eq_zero_iff_expTransport_fixed (hMod A : EndH) :
    relativeModularDeriv (E := E) hMod A = 0 ↔
      ∀ t : ℝ, expTransport (relativeModularKGenerator (E := E) hMod) A t = A := by
  constructor
  · intro hKernel t
    exact expTransport_eq_self_of_relativeModularDeriv_eq_zero hMod A t hKernel
  · intro hFixed
    have hPath :
        (fun t : ℝ => expTransport (relativeModularKGenerator (E := E) hMod) A t) =
          fun _ : ℝ => A := funext hFixed
    have hDeriv := hasDerivAt_expTransport_at_zero
      (relativeModularKGenerator (E := E) hMod) A
    rw [hPath] at hDeriv
    have hZero := hDeriv.unique (hasDerivAt_const (0 : ℝ) A)
    simpa only [relativeModularDeriv, modularDeriv, relativeModularKGenerator,
      lieBracket_eq_transportCommutator] using hZero

end CompleteFlow

/-- The commutator Lip-1 condition is the unit bound on the actual modular
derivation. -/
theorem lipschitzFunction_iff (hMod A : EndH) :
    (souriauSpectralData hMod).LipschitzFunction A ↔
      ‖relativeModularDeriv (E := E) hMod A‖ ≤ 1 := Iff.rfl

/-- Quantitative boundedness of the noncommutative modular derivation. -/
theorem norm_relativeModularDeriv_le (hMod A : EndH) :
    ‖relativeModularDeriv (E := E) hMod A‖ ≤
      2 * ‖relativeModularKGenerator (E := E) hMod‖ * ‖A‖ := by
  have hBound := (souriauSpectralData hMod).commutatorNorm_le A
  rw [commutatorNorm_eq] at hBound
  simpa only [souriauSpectralData] using hBound

/-- Global Lipschitz regularity in the observable, at the explicit operator
bound `2 * ‖G‖`. No regularity in the seed or state is assumed here. -/
theorem lipschitzWith_relativeModularDeriv (hMod : EndH) :
    LipschitzWith (2 * ‖relativeModularKGenerator (E := E) hMod‖₊)
      (relativeModularDeriv (E := E) hMod) := by
  exact (souriauSpectralData hMod).lipschitzWith_commutator

/-- The norm of the relative modular derivation has the same explicit
Lipschitz bound as the derivation itself. -/
theorem lipschitzWith_norm_relativeModularDeriv (hMod : EndH) :
    LipschitzWith (2 * ‖relativeModularKGenerator (E := E) hMod‖₊)
      (fun A : EndH => ‖relativeModularDeriv (E := E) hMod A‖) := by
  exact (souriauSpectralData hMod).lipschitzWith_commutatorNorm

/-- A bounded real probe preserves quantitative control of the modular
response, with the probe's operator norm included in the constant. -/
theorem lipschitzWith_probed_relativeModularDeriv
    (hMod : EndH) (ω : EndH →L[ℝ] ℝ) :
    LipschitzWith
      (‖ω‖₊ * (2 * ‖relativeModularKGenerator (E := E) hMod‖₊))
      (fun A : EndH => ω (relativeModularDeriv (E := E) hMod A)) := by
  exact ω.lipschitzWith.comp (lipschitzWith_relativeModularDeriv hMod)

section CompleteIsometry

variable [CompleteSpace E]

/-- Self-adjointness and phase-linearity of the seed make the actual
state transport an isometry for the positive doubled Hilbert norm. -/
theorem isometry_modularTransportFlow
    (hMod : EndH) (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod) (t : ℝ) :
    Isometry (modularTransportFlow (E := E) hMod t) := by
  exact (((modularTransportFlow (E := E) hMod t).toLinearMap).isometryOfInner
    (modularTransportFlow_preserves_inner_of_isSelfAdjoint_of_IsPhaseLinear
      hMod hSelf hPhase t)).isometry

/-- Positive-Hilbert isometric transport has the native Lipschitz constant
one. Preservation of the indefinite Krein form alone is not its premise. -/
theorem lipschitzWith_modularTransportFlow
    (hMod : EndH) (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod) (t : ℝ) :
    LipschitzWith 1 (modularTransportFlow (E := E) hMod t) :=
  (isometry_modularTransportFlow hMod hSelf hPhase t).lipschitzWith

end CompleteIsometry

/-- An admissible observable contributes to the existing real supremum
only with the boundedness premise required by its owner. -/
theorem observable_le_spectral_distance_supremum
    (hMod A : EndH) (ω₁ ω₂ : EndH → ℝ)
    (hLip : ‖relativeModularDeriv (E := E) hMod A‖ ≤ 1)
    (hBdd : BddAbove
      (ConnesNCSpectralMetricSupremum.spectralDistanceSet
        (relativeModularKGenerator (E := E) hMod) ω₁ ω₂)) :
    |ω₁ A - ω₂ A| ≤
      ConnesNCSpectralMetricSupremum.supremumSpectralDist
        (relativeModularKGenerator (E := E) hMod) ω₁ ω₂ := by
  apply ConnesNCSpectralMetricSupremum.pointwise_le_supremum_spectral_dist
    (relativeModularKGenerator (E := E) hMod) ω₁ ω₂ A ?_ hBdd
  change (souriauSpectralData hMod).LipschitzFunction A
  exact (lipschitzFunction_iff hMod A).2 hLip

/-- Distinguishing a stationary observable forces the spectral-distance
value set to be unbounded. This statement does not assign `+∞` to a real
supremum. -/
theorem spectralDistanceSet_not_bddAbove_of_relativeModularDeriv_eq_zero
    (hMod A : EndH) (ω₁ ω₂ : EndH →+ ℝ)
    (hKernel : relativeModularDeriv (E := E) hMod A = 0)
    (hReadout : ω₁ A ≠ ω₂ A) :
    ¬ BddAbove
      (ConnesNCSpectralMetricSupremum.spectralDistanceSet
        (relativeModularKGenerator (E := E) hMod) ω₁ ω₂) := by
  apply ConnesNCSpectralMetricSupremum.spectralDistanceSet_not_bddAbove_of_commuting_readouts
    (relativeModularKGenerator (E := E) hMod) ω₁ ω₂ A ?_ hReadout
  change (souriauSpectralData hMod).commutator A = 0
  simpa only [commutator_eq_relativeModularDeriv] using hKernel

/-- Finite bounded spectral-distance values require the two additive
readouts to agree on every stationary observable. -/
theorem readouts_eq_on_relativeModularDeriv_kernel_of_bddAbove
    (hMod A : EndH) (ω₁ ω₂ : EndH →+ ℝ)
    (hBdd : BddAbove
      (ConnesNCSpectralMetricSupremum.spectralDistanceSet
        (relativeModularKGenerator (E := E) hMod) ω₁ ω₂))
    (hKernel : relativeModularDeriv (E := E) hMod A = 0) :
    ω₁ A = ω₂ A := by
  by_contra hReadout
  exact spectralDistanceSet_not_bddAbove_of_relativeModularDeriv_eq_zero
    hMod A ω₁ ω₂ hKernel hReadout hBdd

end InfoGeometry.Canonical.SouriauKillingLipschitzBridge
