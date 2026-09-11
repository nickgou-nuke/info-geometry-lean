import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform

/-!
# Mellin and wavelet transport in logarithmic scale

This owner records the elementary, kernel-checkable part of the logarithmic
scale dictionary.  Positive multiplicative scales are transported to additive
log-time, and wavelet translations act by the additive group law.  Analytic
Mellin inversion, admissibility, and conformal-field-theoretic statements are
not asserted here.
-/

noncomputable section

namespace InfoGeometry.Analysis.MellinWaveletConformalMapping

open InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform

/-- Additive logarithmic time attached to a positive multiplicative scale. -/
def logarithmicTime (t : ℝ) : ℝ := Real.log t

/-- Multiplicative scale obtained from additive logarithmic time. -/
def multiplicativeScale (τ : ℝ) : ℝ := Real.exp τ

theorem multiplicativeScale_log (t : ℝ) (ht : 0 < t) :
    multiplicativeScale (logarithmicTime t) = t := by
  exact Real.exp_log ht

theorem logarithmicTime_multiplicativeScale (τ : ℝ) :
    logarithmicTime (multiplicativeScale τ) = τ := by
  exact Real.log_exp τ

/-- The positive multiplicative scale axis is homeomorphic to additive log-time. -/
noncomputable def positiveScaleExpHomeomorph :
    ℝ ≃ₜ Set.Ioi (0 : ℝ) :=
  (Homeomorph.Set.univ ℝ).symm.trans
    Real.expPartialHomeomorph.toHomeomorphSourceTarget

/-- The inverse coordinate change from positive scales to log-time. -/
noncomputable def positiveScaleLogHomeomorph :
    Set.Ioi (0 : ℝ) ≃ₜ ℝ :=
  (positiveScaleExpHomeomorph).symm

@[simp] theorem positiveScaleExpHomeomorph_apply (τ : ℝ) :
    positiveScaleExpHomeomorph τ =
      ⟨multiplicativeScale τ, Real.exp_pos τ⟩ := rfl

@[simp] theorem positiveScaleLogHomeomorph_apply (t : Set.Ioi (0 : ℝ)) :
    positiveScaleLogHomeomorph t = logarithmicTime t := by
  rfl

/-- Pull a scale signal back to additive logarithmic time. -/
def logTimePullback (f : ℝ → ℂ) : ℝ → ℂ :=
  fun τ => f (multiplicativeScale τ)

theorem continuous_logTimePullback
    (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (logTimePullback f) := by
  exact hf.comp Real.continuous_exp

theorem logTimePullback_at_log (f : ℝ → ℂ) (t : ℝ) (ht : 0 < t) :
    logTimePullback f (logarithmicTime t) = f t := by
  simp [logTimePullback, multiplicativeScale_log t ht]

/-- Translation of a wavelet or test signal in additive log-time. -/
def waveletTranslate (ψ : ℝ → ℂ) (τ : ℝ) : ℝ → ℂ :=
  fun x => ψ (x - τ)

theorem continuous_waveletTranslate
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (τ : ℝ) :
    Continuous (waveletTranslate ψ τ) := by
  exact hψ.comp (continuous_id.sub continuous_const)

theorem waveletTranslate_zero (ψ : ℝ → ℂ) :
    waveletTranslate ψ 0 = ψ := by
  funext x
  simp [waveletTranslate]

theorem waveletTranslate_add (ψ : ℝ → ℂ) (τ σ : ℝ) :
    waveletTranslate (waveletTranslate ψ τ) σ =
      waveletTranslate ψ (τ + σ) := by
  funext x
  simp only [waveletTranslate]
  congr 1
  ring

/-- The existing Mellin/Laplace owner supplies the logarithmic pullback law. -/
theorem mellin_wavelet_scale_shape_compatibility
    (P : LaplaceMellinScaleShapePacket) :
    P.scaleChannel = P.shapeChannel := by
  exact P.mellinScaleCompatible

end InfoGeometry.Analysis.MellinWaveletConformalMapping
