import InfoGeometry.Canonical.CalabiYauMetricRicci

namespace InfoGeometry.Canonical.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.SpectralInference

section WBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Constructive Calabi-Yau spectral closure state:
constant Monge-Ampere density together with vanishing spinorial scalar curvature.
-/
def MongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E) : Prop :=
  HasConstantMongeAmpereDensity IST.H ∧ spinorialScalarCurvature IST = 0

/-- Constructive spectral Calabi-Yau state (non-bridge form). -/
def CalabiYauSpinorialState (IST : InfoSpectralTriple E) : Prop :=
  spinorialScalarCurvature IST = 0

/-- Constructor for the spinorial closure state. -/
private theorem mongeAmpereSpinorialClosure_mk
    (IST : InfoSpectralTriple E)
    (hConst : HasConstantMongeAmpereDensity IST.H)
    (hSpin0 : CalabiYauSpinorialState IST) :
    MongeAmpereSpinorialClosure IST := by
  exact ⟨hConst, hSpin0⟩

/-- Extract spinorial vanishing from the constructive spinorial closure state. -/
private theorem spinorialScalarCurvature_eq_zero_of_mongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E)
    (hCY : MongeAmpereSpinorialClosure IST) :
    CalabiYauSpinorialState IST :=
  hCY.2

/--
Connection to the `W`-flow layer:
under normalized spinorial tracking, the explicit spinorial vanishing
portion of the closure makes `W` constant.
-/
private theorem W_constant_of_spinorialClosureState
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hCY : MongeAmpereSpinorialClosure IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  refine ⟨W 0, ?_⟩
  intro s
  have hDerivZero : ∀ t : ℝ, deriv W t = 0 := by
    intro t
    calc
      deriv W t = |spinorialScalarCurvature IST| := by
        rw [deriv_W_eq_abs_spinorial_of_normalized_tracking
          (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack t]
      _ = 0 := by
        rw [hCY.2]
        simp
  simpa using is_const_of_deriv_eq_zero (f := W) hDiff hDerivZero s 0

/--
Constructive `W`-constancy closure from an explicit zero-spinorial witness
(non-bridge form).
-/
private theorem W_constant_of_spinorialState
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hSpin0 : CalabiYauSpinorialState IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  refine ⟨W 0, ?_⟩
  intro s
  have hDerivZero : ∀ t : ℝ, deriv W t = 0 := by
    intro t
    calc
      deriv W t = |spinorialScalarCurvature IST| := by
        rw [deriv_W_eq_abs_spinorial_of_normalized_tracking
          (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack t]
      _ = 0 := by
        rw [hSpin0]
        simp
  simpa using is_const_of_deriv_eq_zero (f := W) hDiff hDerivZero s 0

end WBridge

end InfoGeometry.Canonical.CalabiYauBridge
