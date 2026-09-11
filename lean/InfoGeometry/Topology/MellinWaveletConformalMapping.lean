import InfoGeometry.Topology.PositiveEnergyMellinKernelTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Logarithmic scale and finite Mellin/wavelet readouts

This is the finite topological layer of the symbolic-scale picture.  Positive
scales are coordinatized by `log`, and the exponential coordinate gives the
inverse chart.  The Mellin statement is only the already available continuous
scalar kernel; no integral transform, inversion, or conformal-block theorem is
claimed here.
-/

noncomputable section

namespace InfoGeometry.Topology

open Set
open InfoGeometry.Canonical

def positiveScale : Set ℝ := Set.Ioi 0

def logScaleCoordinate (t : positiveScale) : ℝ := Real.log t.1

def expScaleCoordinate (τ : ℝ) : positiveScale :=
  ⟨Real.exp τ, Real.exp_pos τ⟩

theorem expScaleCoordinate_logScaleCoordinate (t : positiveScale) :
    expScaleCoordinate (logScaleCoordinate t) = t := by
  apply Subtype.ext
  have ht : 0 < (t : ℝ) := t.property
  simp [expScaleCoordinate, logScaleCoordinate, Real.exp_log ht]

theorem logScaleCoordinate_expScaleCoordinate (τ : ℝ) :
    logScaleCoordinate (expScaleCoordinate τ) = τ := by
  simp [logScaleCoordinate, expScaleCoordinate]

theorem continuousOn_logScaleCoordinate :
    ContinuousOn Real.log positiveScale := by
  apply Real.continuousOn_log.mono
  intro t ht
  exact ne_of_gt ht

theorem continuous_expScaleCoordinate :
    Continuous expScaleCoordinate := by
  exact Continuous.subtype_mk Real.continuous_exp (fun τ => Real.exp_pos τ)

def positiveScaleExpEquiv : ℝ ≃ positiveScale :=
  { toFun := expScaleCoordinate
    invFun := logScaleCoordinate
    left_inv := logScaleCoordinate_expScaleCoordinate
    right_inv := expScaleCoordinate_logScaleCoordinate }

def positiveScaleExpHomeomorph : ℝ ≃ₜ positiveScale := by
  exact Homeomorph.mk positiveScaleExpEquiv
    (continuous_toFun := continuous_expScaleCoordinate)
    (continuous_invFun :=
      continuousOn_iff_continuous_restrict.mp continuousOn_logScaleCoordinate)

def positiveScaleLogHomeomorph : positiveScale ≃ₜ ℝ :=
  positiveScaleExpHomeomorph.symm

@[simp] theorem positiveScaleExpHomeomorph_apply (τ : ℝ) :
    positiveScaleExpHomeomorph τ = expScaleCoordinate τ :=
  rfl

@[simp] theorem positiveScaleLogHomeomorph_apply (t : positiveScale) :
    positiveScaleLogHomeomorph t = logScaleCoordinate t :=
  rfl

theorem positiveScaleExpHomeomorph_symm_apply (t : positiveScale) :
    positiveScaleExpHomeomorph.symm t = logScaleCoordinate t :=
  rfl

theorem positiveScaleLogHomeomorph_symm_apply (τ : ℝ) :
    positiveScaleLogHomeomorph.symm τ = expScaleCoordinate τ :=
  rfl

def logarithmicMellinKernel (p : ℝ × ℝ) : ℝ :=
  mellinKernel (Real.exp p.1) p.2

theorem continuous_logarithmicMellinKernel :
    Continuous logarithmicMellinKernel := by
  unfold logarithmicMellinKernel
  have hscale : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  simpa [Function.comp_def] using
    (InfoGeometry.Topology.continuousOn_mellinKernel.comp_continuous hscale
      (fun p => ⟨Real.exp_pos p.1, Set.mem_univ p.2⟩))

def waveletDilation (τ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (Real.exp τ * t)

theorem continuous_waveletDilation
    (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => waveletDilation p.1 f p.2) := by
  apply hf.comp
  exact (Real.continuous_exp.comp continuous_fst).mul continuous_snd

theorem waveletDilation_zero (f : ℝ → ℝ) :
    waveletDilation 0 f = f := by
  funext t
  simp [waveletDilation]

theorem waveletDilation_add (τ σ : ℝ) (f : ℝ → ℝ) :
    waveletDilation τ (waveletDilation σ f) =
      waveletDilation (τ + σ) f := by
  funext t
  simp [waveletDilation, Real.exp_add, mul_assoc, mul_comm]

theorem mellin_wavelet_scale_readout (τ Δ : ℝ) :
    logarithmicMellinKernel (τ, Δ) =
      mellinKernel (Real.exp τ) Δ :=
  rfl

end InfoGeometry.Topology
