/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Bochner integrals with an internal real phase axis

The kernel is `cos (2 * pi * ξ * x) • v - sin (2 * pi * ξ * x) • K v`,
where `K` is a bounded real-linear operator. Its sign and frequency convention
are those of the negative-exponential Fourier kernel. Integration uses
Lebesgue measure on the real line.

The analytic result is naturality of this integral under bounded real-linear
intertwiners. An intertwiner preserving the phase axis preserves frequency;
an intertwiner reversing the phase axis reverses frequency. Integrability of
the kernel is derived from integrability of the signal, using the bounds on
real sine and cosine. Operator composition remains noncommutative.

The identities require no square law for `K`. Calling `K` a complex structure
additionally requires `K.comp K = -id`; the doubled-carrier adapter supplies
the repository's existing `complex_i`. No inversion or norm-preservation
theorem is asserted here.

The final adapter samples a signal at `exp u` and integrates against `du`.
Its hypothesis is integrability of that logarithmic pullback. A change of
variables to multiplicative Haar measure is a separate analytic statement.
-/

noncomputable section

namespace InfoGeometry.Analysis.InternalPhaseFourier

open MeasureTheory

variable {H G : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The negative-frequency kernel with an internal bounded real phase axis. -/
def fourierKernel (K : H →L[ℝ] H) (ξ x : ℝ) (v : H) : H :=
  Real.cos (2 * Real.pi * ξ * x) • v -
    Real.sin (2 * Real.pi * ξ * x) • K v

/-- The internal-phase Fourier integral with respect to real Lebesgue measure. -/
def fourierIntegral (K : H →L[ℝ] H) (f : ℝ → H) (ξ : ℝ) : H :=
  ∫ x : ℝ, fourierKernel K ξ x (f x)

/-- An integrable signal has an integrable internal-phase kernel at every frequency. -/
theorem integrable_fourierKernel (K : H →L[ℝ] H)
    {f : ℝ → H} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x : ℝ => fourierKernel K ξ x (f x)) := by
  have hangle : Continuous (fun x : ℝ => 2 * Real.pi * ξ * x) :=
    continuous_const.mul continuous_id
  have hcos : Integrable
      (fun x : ℝ => Real.cos (2 * Real.pi * ξ * x) • f x) := by
    apply hf.bdd_smul 1
    · exact (Real.continuous_cos.comp hangle).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using
          Real.abs_cos_le_one (2 * Real.pi * ξ * x))
  have hsin : Integrable
      (fun x : ℝ => Real.sin (2 * Real.pi * ξ * x) • K (f x)) := by
    apply (K.integrable_comp hf).bdd_smul 1
    · exact (Real.continuous_sin.comp hangle).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using
          Real.abs_sin_le_one (2 * Real.pi * ξ * x))
  exact hcos.sub hsin

/-- At frequency zero the kernel reduces to the original signal. -/
theorem fourierIntegral_zero (K : H →L[ℝ] H) (f : ℝ → H) :
    fourierIntegral K f 0 = ∫ x : ℝ, f x := by
  simp only [fourierIntegral, fourierKernel, mul_zero, zero_mul,
    Real.cos_zero, Real.sin_zero, one_smul, zero_smul, sub_zero]

/-- A bounded real-linear intertwiner preserving the phase axis preserves the kernel. -/
theorem map_fourierKernel_of_intertwines
    (K : H →L[ℝ] H) (L : G →L[ℝ] G) (T : H →L[ℝ] G)
    (hTK : T.comp K = L.comp T) (ξ x : ℝ) (v : H) :
    T (fourierKernel K ξ x v) = fourierKernel L ξ x (T v) := by
  have hv : T (K v) = L (T v) := by
    exact congrArg (fun A : H →L[ℝ] G => A v) hTK
  simp only [fourierKernel, map_sub, map_smul, hv]

/-- Reversing the phase axis changes the sign of the frequency in the kernel. -/
theorem map_fourierKernel_of_antiintertwines
    (K : H →L[ℝ] H) (L : G →L[ℝ] G) (T : H →L[ℝ] G)
    (hTK : T.comp K = -(L.comp T)) (ξ x : ℝ) (v : H) :
    T (fourierKernel K ξ x v) = fourierKernel L (-ξ) x (T v) := by
  have hv : T (K v) = -(L (T v)) := by
    exact congrArg (fun A : H →L[ℝ] G => A v) hTK
  simp only [fourierKernel, map_sub, map_smul, hv, mul_neg, neg_mul,
    Real.cos_neg, Real.sin_neg, smul_neg, neg_smul]

/-- A phase-preserving bounded intertwiner commutes with the actual Bochner integral. -/
theorem map_fourierIntegral_of_intertwines
    (K : H →L[ℝ] H) (L : G →L[ℝ] G) (T : H →L[ℝ] G)
    (hTK : T.comp K = L.comp T) {f : ℝ → H}
    (hf : Integrable f) (ξ : ℝ) :
    T (fourierIntegral K f ξ) =
      fourierIntegral L (fun x => T (f x)) ξ := by
  calc
    T (fourierIntegral K f ξ) =
        ∫ x : ℝ, T (fourierKernel K ξ x (f x)) :=
      (T.integral_comp_comm (integrable_fourierKernel K hf ξ)).symm
    _ = fourierIntegral L (fun x => T (f x)) ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x => map_fourierKernel_of_intertwines K L T hTK ξ x (f x))

/-- A phase-reversing bounded intertwiner reverses the frequency of the integral. -/
theorem map_fourierIntegral_of_antiintertwines
    (K : H →L[ℝ] H) (L : G →L[ℝ] G) (T : H →L[ℝ] G)
    (hTK : T.comp K = -(L.comp T)) {f : ℝ → H}
    (hf : Integrable f) (ξ : ℝ) :
    T (fourierIntegral K f ξ) =
      fourierIntegral L (fun x => T (f x)) (-ξ) := by
  calc
    T (fourierIntegral K f ξ) =
        ∫ x : ℝ, T (fourierKernel K ξ x (f x)) :=
      (T.integral_comp_comm (integrable_fourierKernel K hf ξ)).symm
    _ = fourierIntegral L (fun x => T (f x)) (-ξ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x => map_fourierKernel_of_antiintertwines K L T hTK ξ x (f x))

/--
The Mellin phase channel expressed on logarithmic coordinates. The integration
variable is `u` with Lebesgue measure `du`; only positive inputs `exp u` of `f`
are sampled. No equality with a positive-axis `dr / r` integral is asserted.
-/
def logMellinIntegral (K : H →L[ℝ] H) (f : ℝ → H) (ξ : ℝ) : H :=
  ∫ u : ℝ, fourierKernel K ξ u (f (Real.exp u))

/-- Phase-preserving naturality for the integrable logarithmic pullback. -/
theorem map_logMellinIntegral_of_intertwines
    (K : H →L[ℝ] H) (L : G →L[ℝ] G) (T : H →L[ℝ] G)
    (hTK : T.comp K = L.comp T) {f : ℝ → H}
    (hf : Integrable (fun u : ℝ => f (Real.exp u))) (ξ : ℝ) :
    T (logMellinIntegral K f ξ) =
      logMellinIntegral L (fun r => T (f r)) ξ := by
  exact map_fourierIntegral_of_intertwines K L T hTK hf ξ

/-- Phase-reversing naturality for the integrable logarithmic pullback. -/
theorem map_logMellinIntegral_of_antiintertwines
    (K : H →L[ℝ] H) (L : G →L[ℝ] G) (T : H →L[ℝ] G)
    (hTK : T.comp K = -(L.comp T)) {f : ℝ → H}
    (hf : Integrable (fun u : ℝ => f (Real.exp u))) (ξ : ℝ) :
    T (logMellinIntegral K f ξ) =
      logMellinIntegral L (fun r => T (f r)) (-ξ) := by
  exact map_fourierIntegral_of_antiintertwines K L T hTK hf ξ

end InfoGeometry.Analysis.InternalPhaseFourier

end
