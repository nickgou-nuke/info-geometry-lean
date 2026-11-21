/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum
import InfoGeometry.Canonical.ConnesSpectralTripleBridge
import InfoGeometry.Krein.ExponentialIsometry
import InfoGeometry.OperatorAlgebra.KreinInnerDerivation
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Souriau stationarity and Lipschitz control on doubled real Krein spaces

The carrier is the existing doubled real Krein space `DoubledSpace E`, with
fundamental symmetry `spectral_epsilon` and signed pairing
`[(x, ξ), (y, η)] = inner ℝ x y - inner ℝ ξ η`. Its associated positive
Hilbert structure supplies the topology and operator norm.

On this carrier, the relative modular generator
`G = relativeModularKGenerator hMod` acts on observables by the already-owned
inner derivation `relativeModularDeriv hMod A = G * A - A * G`.

This module identifies that derivation with the repository's bounded
commutator-seminorm interface, proves its kernel and Lipschitz consequences,
and transports the existing obstruction to finite spectral distance. It also
connects Krein-skew generators to preservation of the signed pairing,
Krein-adjoint observable sectors, and bounded signed readouts. The norm
throughout is the associated Hilbert operator norm. No complex scalar,
finite matrix carrier, unbounded Dirac
operator, compact-resolvent assertion, or manifold Killing field is added.

The term Killing refers here only to an observable in the kernel of the
relative modular derivation. The higher thermodynamic owner names precisely
this stationarity condition `IsPotentialKillingOperator`; this lower owner
does not import that owner's additional thermodynamic dependency graph.

Stationary observables are fixed at every time by the existing exponential
conjugation, with no self-adjointness or phase-linearity hypothesis needed.
Krein-skewness makes the state transport a Krein isometry. An independent
Hilbert-self-adjoint and phase-linear seed regime gives isometry of the
positive Hilbert norm.
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

/-- The negative sheet grading produces the real sheet-swap generator. -/
@[simp] theorem relativeModularKGenerator_neg_spectral_epsilon :
    relativeModularKGenerator (E := E) (-(spectral_epsilon (E := E))) =
      modular_j (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [relativeModularKGenerator, modularTransportGenerator, clockAxis]

/-- The concrete doubled generator is nonzero on every nontrivial real carrier. -/
theorem relativeModularKGenerator_neg_spectral_epsilon_ne_zero [Nontrivial E] :
    relativeModularKGenerator (E := E) (-(spectral_epsilon (E := E))) ≠ 0 := by
  rw [relativeModularKGenerator_neg_spectral_epsilon]
  intro hZero
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hCoord := congrArg
    (fun A : EndH => WithLp.snd (A (to_doubled x 0))) hZero
  exact hx (by simpa using hCoord)

/-- The concrete real boost acts nontrivially on the sheet grading:
its commutator is twice the real clock axis. -/
@[simp] theorem relativeModularDeriv_neg_spectral_epsilon_spectral_epsilon :
    relativeModularDeriv (E := E) (-(spectral_epsilon (E := E)))
      (spectral_epsilon (E := E)) = (2 : ℝ) • clockAxis (E := E) := by
  change transportCommutator
      (relativeModularKGenerator (E := E) (-(spectral_epsilon (E := E))))
      (spectral_epsilon (E := E)) = (2 : ℝ) • clockAxis (E := E)
  rw [relativeModularKGenerator_neg_spectral_epsilon]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [transportCommutator, clockAxis, two_smul, sub_eq_add_neg]

/-- The concrete boost derivation is nonzero on every nontrivial carrier. -/
theorem relativeModularDeriv_neg_spectral_epsilon_spectral_epsilon_ne_zero
    [Nontrivial E] :
    relativeModularDeriv (E := E) (-(spectral_epsilon (E := E)))
      (spectral_epsilon (E := E)) ≠ 0 := by
  rw [relativeModularDeriv_neg_spectral_epsilon_spectral_epsilon]
  intro hZero
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hCoord := congrArg
    (fun A : EndH => WithLp.snd (A (to_doubled x 0))) hZero
  have hTwo : (2 : ℝ) • x = 0 := by simpa using hCoord
  exact hx ((smul_eq_zero.mp hTwo).resolve_left (by norm_num))

/-- Every bounded modular state flow has a finite native Lipschitz bound
given by its operator norm, including non-Hilbert-isometric Krein flows. -/
theorem lipschitzWith_modularTransportFlow_opNorm (hMod : EndH) (t : ℝ) :
    LipschitzWith ‖modularTransportFlow (E := E) hMod t‖₊
      (modularTransportFlow (E := E) hMod t) :=
  (modularTransportFlow (E := E) hMod t).lipschitzWith

section CompleteKrein

variable [CompleteSpace E]

local instance : KreinSpace H₂ := instKreinSpaceProdL2 (E := E)

/-- The actual relative modular generator has Krein adjoint `K ∘ hMod♯`. -/
theorem kreinAdjoint_relativeModularKGenerator (hMod : EndH) :
    KreinSpace.kreinAdjoint (relativeModularKGenerator (E := E) hMod) =
      (clockAxis (E := E)).comp (KreinSpace.kreinAdjoint hMod) := by
  simp only [relativeModularKGenerator, modularTransportGenerator,
    KreinSpace.kreinAdjoint_comp, clockAxis, kreinAdjoint_complex_i]

/-- Exact seed condition for Krein skew-adjointness of the existing generator. -/
theorem isKreinSkewAdjoint_relativeModularKGenerator_iff (hMod : EndH) :
    KreinSpace.IsKreinSkewAdjoint (relativeModularKGenerator (E := E) hMod) ↔
      (clockAxis (E := E)).comp (KreinSpace.kreinAdjoint hMod) =
        -(hMod.comp (clockAxis (E := E))) := by
  change
    KreinSpace.kreinAdjoint (relativeModularKGenerator (E := E) hMod) =
        -(hMod.comp (clockAxis (E := E))) ↔
      (clockAxis (E := E)).comp (KreinSpace.kreinAdjoint hMod) =
        -(hMod.comp (clockAxis (E := E)))
  rw [kreinAdjoint_relativeModularKGenerator]

/-- A Krein-self-adjoint, phase-antilinear seed gives an infinitesimal
isometry of the indefinite doubled pairing. -/
theorem isKreinSkewAdjoint_relativeModularKGenerator_of_isKreinSelfAdjoint_of_IsPhaseAntilinear
    (hMod : EndH)
    (hSelf : KreinSpace.IsKreinSelfAdjoint hMod)
    (hAnti : IsPhaseAntilinear (E := E) hMod) :
    KreinSpace.IsKreinSkewAdjoint (relativeModularKGenerator (E := E) hMod) := by
  apply (isKreinSkewAdjoint_relativeModularKGenerator_iff hMod).2
  change KreinSpace.kreinAdjoint hMod = hMod at hSelf
  rw [hSelf]
  change hMod.comp (clockAxis (E := E)) =
    -((clockAxis (E := E)).comp hMod) at hAnti
  simpa only [neg_neg] using congrArg Neg.neg hAnti.symm

/-- The concrete sheet-swap generator is Krein-skew by the doubled owner. -/
theorem isKreinSkewAdjoint_relativeModularKGenerator_neg_spectral_epsilon :
    KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) (-(spectral_epsilon (E := E)))) := by
  rw [relativeModularKGenerator_neg_spectral_epsilon]
  exact isKreinSkewAdjoint_modular_j (E := E)

/-- The actual modular exponential preserves the doubled signed pairing
when its generator is Krein-skew-adjoint. -/
theorem isKreinIsometry_modularTransportFlow
    (hMod : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod)) (t : ℝ) :
    KreinSpace.IsKreinIsometry (modularTransportFlow (E := E) hMod t) := by
  exact exp_preservesMetric (relativeModularKGenerator (E := E) hMod) hGenerator t

/-- The negative-grading seed yields an actual Krein-isometric boost flow. -/
theorem isKreinIsometry_modularTransportFlow_neg_spectral_epsilon (t : ℝ) :
    KreinSpace.IsKreinIsometry
      (modularTransportFlow (E := E) (-(spectral_epsilon (E := E))) t) :=
  isKreinIsometry_modularTransportFlow (-(spectral_epsilon (E := E)))
    isKreinSkewAdjoint_relativeModularKGenerator_neg_spectral_epsilon t

/-- The invariant is the difference of the two real sheet pairings. -/
theorem modularTransportFlow_preserves_doubled_pairing
    (hMod : EndH)
    (hGenerator : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod))
    (t : ℝ) (x ξ y η : E) :
    KreinSpace.kreinInner
      (modularTransportFlow (E := E) hMod t (to_doubled x ξ))
      (modularTransportFlow (E := E) hMod t (to_doubled y η)) =
      inner ℝ x y - inner ℝ ξ η := by
  rw [isKreinIsometry_modularTransportFlow hMod hGenerator t]
  exact kreinInner_to_doubled x ξ y η

/-- Evaluation against two fixed vectors in the doubled real Krein pairing
is Lipschitz in the observable for the positive Hilbert operator norm. -/
theorem lipschitzWith_kreinReadout (u v : H₂) :
    LipschitzWith (‖u‖₊ * ‖v‖₊)
      (fun A : EndH => KreinSpace.kreinInner (A u) v) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  calc
    dist (KreinSpace.kreinInner (A u) v) (KreinSpace.kreinInner (B u) v)
        = |KreinSpace.kreinInner ((A - B) u) v| := by
            rw [Real.dist_eq]
            congr 1
            simp only [sub_apply,
              KreinSpace.kreinInner_def, map_sub, inner_sub_left]
    _ ≤ ‖(A - B) u‖ * ‖v‖ := KreinSpace.abs_kreinInner_le_norm _ _
    _ ≤ (‖A - B‖ * ‖u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((A - B).le_opNorm u) (norm_nonneg v)
    _ = ((‖u‖₊ * ‖v‖₊ : NNReal) : ℝ) * dist A B := by
      simp only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm]
      ring

/-- The actual Krein readout of the relative modular response has the
product of the pairing bound and the commutator Lipschitz bound. -/
theorem lipschitzWith_krein_relativeModularDeriv
    (hMod : EndH) (u v : H₂) :
    LipschitzWith
      ((‖u‖₊ * ‖v‖₊) *
        (2 * ‖relativeModularKGenerator (E := E) hMod‖₊))
      (fun A : EndH =>
        KreinSpace.kreinInner ((relativeModularDeriv (E := E) hMod A) u) v) := by
  exact (lipschitzWith_kreinReadout u v).comp
    (lipschitzWith_relativeModularDeriv hMod)

/-- A Krein-skew-adjoint generator makes the relative modular derivation
commute with the Krein adjoint. -/
theorem kreinAdjoint_relativeModularDeriv
    (hMod A : EndH)
    (hG : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod)) :
    KreinSpace.kreinAdjoint (relativeModularDeriv (E := E) hMod A) =
      relativeModularDeriv (E := E) hMod (KreinSpace.kreinAdjoint A) := by
  simpa only [InfoGeometry.OperatorAlgebra.kreinCommutator_apply,
    InfoGeometry.OperatorAlgebra.kreinAdjoint, relativeModularDeriv,
    modularDeriv, transportCommutator, relativeModularKGenerator,
    ContinuousLinearMap.mul_def] using
    (InfoGeometry.OperatorAlgebra.kreinCommutator_kreinStar
      (relativeModularKGenerator (E := E) hMod) A hG).symm

/-- The relative modular derivation preserves Krein-self-adjoint observables
when its generator is Krein-skew-adjoint. -/
theorem isKreinSelfAdjoint_relativeModularDeriv
    (hMod A : EndH)
    (hG : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod))
    (hA : KreinSpace.IsKreinSelfAdjoint A) :
    KreinSpace.IsKreinSelfAdjoint (relativeModularDeriv (E := E) hMod A) := by
  change KreinSpace.kreinAdjoint (relativeModularDeriv (E := E) hMod A) =
    relativeModularDeriv (E := E) hMod A
  rw [kreinAdjoint_relativeModularDeriv hMod A hG]
  exact congrArg (relativeModularDeriv (E := E) hMod) hA

/-- The same derivation preserves the Krein-skew-adjoint sector, by the
existing Lie algebra closure of Krein-skew-adjoint endomorphisms. -/
theorem isKreinSkewAdjoint_relativeModularDeriv
    (hMod A : EndH)
    (hG : KreinSpace.IsKreinSkewAdjoint
      (relativeModularKGenerator (E := E) hMod))
    (hA : KreinSpace.IsKreinSkewAdjoint A) :
    KreinSpace.IsKreinSkewAdjoint (relativeModularDeriv (E := E) hMod A) := by
  change KreinSpace.IsKreinSkewAdjoint
    (transportCommutator (relativeModularKGenerator (E := E) hMod) A)
  rw [← lieBracket_eq_transportCommutator]
  exact KreinSpace.isKreinSkewAdjoint_lie hG hA

end CompleteKrein

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
