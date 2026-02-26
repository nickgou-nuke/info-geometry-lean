import InfoGeometry.Canonical.Promoted.RicciMongeAmpere
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace InfoGeometry.Research.PerelmanW

open InfoGeometry.Research.RicciMongeAmpere
open InfoGeometry.Research.SpectralInference

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Perelman-style entropy functional scaffold along a scalar Ricci flow:
`W(Λ) = τ(Λ) * R(Λ) + f(Λ)`.
-/
def WFunctional
    (flow : ScalarRicciFlow E) (τ f : ℝ → ℝ) (scale : ℝ) : ℝ :=
  τ scale * flow scale + f scale

/-- Dissipation rate `dW/dΛ`. -/
noncomputable def WDissipation
    (flow : ScalarRicciFlow E) (τ f : ℝ → ℝ) (scale : ℝ) : ℝ :=
  deriv (fun s => WFunctional flow τ f s) scale

/--
Abstract law identifying the `W`-dissipation with a prescribed nonnegative source.
-/
def SatisfiesWLaw
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, WDissipation flow τ f s = diss s

lemma deriv_WFunctional_eq_of_law
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ)
    (hLaw : SatisfiesWLaw flow τ f diss) (s : ℝ) :
    deriv (fun t => WFunctional flow τ f t) s = diss s := by
  simpa [WDissipation] using hLaw s

/--
Monotonicity of `W` from a nonnegative dissipation law.
-/
theorem WFunctional_monotone_of_nonneg_dissipation
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ)
    (hDiff : Differentiable ℝ (fun t => WFunctional flow τ f t))
    (hLaw : SatisfiesWLaw flow τ f diss)
    (hNonneg : ∀ s : ℝ, 0 ≤ diss s) :
    Monotone (fun t => WFunctional flow τ f t) := by
  apply monotone_of_deriv_nonneg hDiff
  intro s
  rw [deriv_WFunctional_eq_of_law flow τ f diss hLaw s]
  exact hNonneg s

/--
Strict monotonicity of `W` from strictly positive dissipation law.
-/
theorem WFunctional_strictMono_of_pos_dissipation
    (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ)
    (hLaw : SatisfiesWLaw flow τ f diss)
    (hPos : ∀ s : ℝ, 0 < diss s) :
    StrictMono (fun t => WFunctional flow τ f t) := by
  apply strictMono_of_deriv_pos
  intro s
  rw [deriv_WFunctional_eq_of_law flow τ f diss hLaw s]
  exact hPos s

end Core

section SpinorialBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Canonical spinorial dissipation proxy for scalar Ricci flow:
absolute value of the scalar beta function.
-/
noncomputable def spinorialWDissipation
    (flow : ScalarRicciFlow E) (_IST : InfoSpectralTriple E) (scale : ℝ) : ℝ :=
  |scalarRicciBetaFunction (E := E) flow scale|

lemma spinorialWDissipation_eq_abs_spinorial_of_normalized_tracking
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (s : ℝ)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST) :
    spinorialWDissipation flow IST s = |spinorialScalarCurvature IST| := by
  unfold spinorialWDissipation
  rw [normalizedKaehlerRicci_beta_eq_neg_spinorial
      (E := E) (flow := flow) (IST := IST) (s := s) hNorm hTrack]
  simp [abs_neg]

/--
If `W` follows the spinorial dissipation law under normalized tracking flow,
its derivative is the constant `|spinorialScalarCurvature|`.
-/
theorem deriv_W_eq_abs_spinorial_of_normalized_tracking
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST) :
    ∀ s : ℝ, deriv W s = |spinorialScalarCurvature IST| := by
  intro s
  rw [hW s, spinorialWDissipation_eq_abs_spinorial_of_normalized_tracking
      (E := E) (flow := flow) (IST := IST) (s := s) hNorm hTrack]

/--
Monotonicity of `W` for the normalized spinorial-tracking flow.
-/
theorem W_monotone_of_spinorial_normalized_tracking
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST) :
    Monotone W := by
  apply monotone_of_deriv_nonneg hDiff
  intro s
  rw [deriv_W_eq_abs_spinorial_of_normalized_tracking
      (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack s]
  exact abs_nonneg _

/--
Strict monotonicity of `W` when the spinorial scalar curvature is nonzero.
-/
theorem W_strictMono_of_spinorial_nonzero
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hSpin : spinorialScalarCurvature IST ≠ 0) :
    StrictMono W := by
  apply strictMono_of_deriv_pos
  intro s
  rw [deriv_W_eq_abs_spinorial_of_normalized_tracking
      (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack s]
  exact abs_pos.mpr hSpin

/--
If the tracked spinorial scalar is zero, any `W` obeying the spinorial law is constant.
-/
theorem W_constant_of_spinorial_zero
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hSpin0 : spinorialScalarCurvature IST = 0) :
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

end SpinorialBridge

end InfoGeometry.Research.PerelmanW
