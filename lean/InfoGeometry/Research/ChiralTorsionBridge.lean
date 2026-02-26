import InfoGeometry.Assumptions.DualConnections
import InfoGeometry.Research.BeliefDynamics
import InfoGeometry.Research.ConformalUnification
import InfoGeometry.Research.InformationTorsion
import InfoGeometry.Convex.ProjectiveRays
import InfoGeometry.Twistor.NullProjective
import InfoGeometry.generalizedKL

/-!
# Research.ChiralTorsionBridge

Bridge layer for the research narrative:

- chiral anomaly sector as a torsion source witness
- negative-log Radon-Nikodym ratio as relative-volume divergence
- Gibbs smoothing over generalized KL for unnormalized states
- projective/twistor null-ray interface for vacuum-apex representatives

All statements remain hypothesis-driven and build-safe.
-/

namespace InfoGeometry.Research.ChiralTorsionBridge

open InfoGeometry.Assumptions.DualConnections
open InfoGeometry.Convex
open InfoGeometry.Research.BeliefDynamics
open InfoGeometry.Research.ConformalUnification
open InfoGeometry.Research.InformationTorsion
open InfoGeometry.Twistor

section VolumeRN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Relative-volume ratio surrogate from the Radon-Nikodym operator. -/
noncomputable def relativeVacuumVolume
    (H : HessianGeometry E) (x y : E) : ℝ :=
  radonNikodymOp H x y

/-- Boltzmann entropy surrogate of relative-volume change: `-log(dμ/dν)`. -/
noncomputable def boltzmannRelativeVolumeEntropy
    (H : HessianGeometry E) (x y : E) : ℝ :=
  -Real.log (relativeVacuumVolume H x y)

omit [FiniteDimensional ℝ E] in
/-- In this model, `-log RN` is exactly the Hessian/Bregman divergence. -/
lemma boltzmannRelativeVolumeEntropy_eq_divergence
    (H : HessianGeometry E) (x y : E) :
    boltzmannRelativeVolumeEntropy H x y = H.divergence x y := by
  unfold boltzmannRelativeVolumeEntropy relativeVacuumVolume radonNikodymOp
  simp

end VolumeRN

section GeneralizedKL

variable {α : Type*} [Fintype α]

/-- Gibbs regularizer induced by generalized (unnormalized) KL energy. -/
noncomputable def gibbsSmoothingOnGeneralizedKL
    (β : ℝ) (μ ν μ₀ : α → ℝ) : ℝ :=
  Real.exp (-β * generalizedKL μ ν μ₀)

lemma gibbsSmoothingOnGeneralizedKL_pos
    (β : ℝ) (μ ν μ₀ : α → ℝ) :
    0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  unfold gibbsSmoothingOnGeneralizedKL
  exact Real.exp_pos _

lemma gibbsSmoothingOnGeneralizedKL_nonneg
    (β : ℝ) (μ ν μ₀ : α → ℝ) :
    0 ≤ gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  exact (gibbsSmoothingOnGeneralizedKL_pos β μ ν μ₀).le

end GeneralizedKL

section ProjectiveTwistor

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unnormalized representative of a projective knowledge ray. -/
abbrev UnnormalizedProjectiveState := NonzeroDoubledState (E := E)

/-- Vacuum-apex null condition on a nonzero doubled representative. -/
def IsVacuumApexNull
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E)) : Prop :=
  Q v.1 = 0

/-- A null unnormalized representative defines a canonical twistor point. -/
noncomputable def vacuumApexTwistor
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E))
    (hNull : IsVacuumApexNull (E := E) Q v) :
    DoubledTwistorSpace (E := E) Q :=
  doubledTwistorMk (E := E) Q v.1 v.2 hNull

end ProjectiveTwistor

section ChiralTorsionChentsov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Θ α : Type*} [Fintype α]

/--
Compatibility package for the research claim:
chiral sector, torsion witness, Chentsov availability, and Gibbs smoothing.
-/
structure ChiralTorsionChentsovGibbsBridge
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ) : Prop where
  anomaly_induces_torsion :
    CI.IsChiralInference → informationTorsion T.dual.nabla ≠ 0
  chentsov_available :
    amariChentsovTensor p
  gibbs_smoothing_pos :
    0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀

/-- Canonical naming alias for the chiral-torsion/Chentsov/Gibbs compatibility package. -/
abbrev ChiralTorsionChentsovGibbsState
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ) : Prop :=
  ChiralTorsionChentsovGibbsBridge CI T p β μ ν μ₀

lemma twistedInference_torsion_nonzero
    (T : TwistedInference E) :
    informationTorsion T.dual.nabla ≠ 0 :=
  T.has_torsion

theorem torsion_nonzero_of_chiral
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hBridge : ChiralTorsionChentsovGibbsBridge CI T p β μ ν μ₀)
    (hChiral : CI.IsChiralInference) :
    informationTorsion T.dual.nabla ≠ 0 :=
  hBridge.anomaly_induces_torsion hChiral

theorem chentsov_and_gibbs_of_bridge
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hBridge : ChiralTorsionChentsovGibbsBridge CI T p β μ ν μ₀) :
    amariChentsovTensor p ∧ 0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  exact ⟨hBridge.chentsov_available, hBridge.gibbs_smoothing_pos⟩

theorem chentsov_and_gibbs_of_state
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hState : ChiralTorsionChentsovGibbsState CI T p β μ ν μ₀) :
    amariChentsovTensor p ∧ 0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  exact chentsov_and_gibbs_of_bridge
    (CI := CI) (T := T) (p := p) (β := β) (μ := μ) (ν := ν) (μ₀ := μ₀) hState

end ChiralTorsionChentsov

end InfoGeometry.Research.ChiralTorsionBridge
