import InfoGeometry.Canonical.ChiralTorsionGeneralizedKL
import InfoGeometry.Canonical.DualConnectionsCore
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.InformationTorsion

namespace InfoGeometry.Canonical.ChiralTorsionBridge

open InfoGeometry.Canonical.DualConnections
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.InformationTorsion

section ChiralTorsionChentsov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Θ α : Type*} [Fintype α]

/-- Constructive chiral-torsion/Chentsov/Gibbs state (fully explicit). -/
def ChiralTorsionChentsovGibbsState
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ) : Prop :=
  (CI.IsChiralInference → informationTorsion T.dual.nabla ≠ 0) ∧
    amariChentsovTensor p ∧
    0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀

/--
Constructive builder: package explicit torsion/Chentsov/Gibbs witnesses into the
canonical chiral-torsion state.
-/
def chiralTorsionChentsovGibbsState_mk
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hTorsion : CI.IsChiralInference → informationTorsion T.dual.nabla ≠ 0)
    (hChentsov : amariChentsovTensor p)
    (hGibbs : 0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀) :
    ChiralTorsionChentsovGibbsState CI T p β μ ν μ₀ := by
  exact ⟨hTorsion, hChentsov, hGibbs⟩

/--
Constructive default builder:
for twisted inference, torsion is already nonzero, so only Chentsov availability
is required; Gibbs positivity is canonical from the exponential model.
-/
def chiralTorsionChentsovGibbsState_of_twistedInference
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hChentsov : amariChentsovTensor p) :
    ChiralTorsionChentsovGibbsState CI T p β μ ν μ₀ :=
  chiralTorsionChentsovGibbsState_mk
    (CI := CI) (T := T) (p := p) (β := β) (μ := μ) (ν := ν) (μ₀ := μ₀)
    (hTorsion := fun _hChiral => T.has_torsion)
    (hChentsov := hChentsov)
    (hGibbs := gibbsSmoothingOnGeneralizedKL_pos β μ ν μ₀)

/-- Lemma `twistedInference_torsion_nonzero`. -/
lemma twistedInference_torsion_nonzero
    (T : TwistedInference E) :
    informationTorsion T.dual.nabla ≠ 0 :=
  T.has_torsion

/-- Theorem `torsion_nonzero_of_chiral`. -/
theorem torsion_nonzero_of_chiral
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hState : ChiralTorsionChentsovGibbsState CI T p β μ ν μ₀)
    (hChiral : CI.IsChiralInference) :
    informationTorsion T.dual.nabla ≠ 0 :=
  hState.1 hChiral

/-- Theorem `chentsov_and_gibbs_of_state`. -/
theorem chentsov_and_gibbs_of_state
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hState : ChiralTorsionChentsovGibbsState CI T p β μ ν μ₀) :
    amariChentsovTensor p ∧ 0 < gibbsSmoothingOnGeneralizedKL β μ ν μ₀ := by
  exact ⟨hState.2.1, hState.2.2⟩

/-- Theorem `torsion_nonzero_of_state_and_chiral`. -/
theorem torsion_nonzero_of_state_and_chiral
    (CI : ConformalInference E)
    (T : TwistedInference E)
    (p : Θ → InfoGeometry.FinProb α)
    (β : ℝ) (μ ν μ₀ : α → ℝ)
    (hState : ChiralTorsionChentsovGibbsState CI T p β μ ν μ₀)
    (hChiral : CI.IsChiralInference) :
    informationTorsion T.dual.nabla ≠ 0 :=
  torsion_nonzero_of_chiral
    (CI := CI) (T := T) (p := p) (β := β) (μ := μ) (ν := ν) (μ₀ := μ₀) hState hChiral

end ChiralTorsionChentsov

end InfoGeometry.Canonical.ChiralTorsionBridge
