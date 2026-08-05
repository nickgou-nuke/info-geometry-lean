import Mathlib.Analysis.MellinTransform
import InfoGeometry.Analysis.MellinWaveletConformalMapping

/-!
# Wavelet admissibility on the Mellin scale

This owner records the analytic admissibility predicate for a wavelet energy
density as Mellin convergence at exponent `0`.  It does not claim Mellin
inversion or a full wavelet admissibility theorem; it only packages the native
convergence condition and its stability under positive dilation.
-/

noncomputable section

namespace InfoGeometry.Analysis.WaveletAdmissibilityCondition

open scoped BigOperators
open InfoGeometry.Analysis.MellinWaveletConformalMapping

/--
Wavelet energy density on the positive scale axis.

For a frequency profile `ψ̂`, the classical admissibility integral is
`∫_{0}^{∞} |ψ̂(ω)|² / ω dω`.  In Mellin form this is the convergence of the
energy density at exponent `0`.
-/
def waveletEnergyDensity (ψHat : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ((‖ψHat t‖ ^ 2 : ℝ) : ℂ)

/--
Wavelet admissibility as Mellin convergence at exponent `0`.

This matches the standard `|ψ̂(ω)|² / ω` admissibility density on the positive
scale axis.
-/
def waveletAdmissible (ψHat : ℝ → ℂ) : Prop :=
  MellinConvergent (waveletEnergyDensity ψHat) 0

/--
Bundle a frequency profile with its admissibility witness.

This is a theorem-safe owner packet: it records admissibility once, without
claiming a derived inversion theorem.
-/
abbrev WaveletAdmissibilityPacket :=
  {ψHat : ℝ → ℂ // waveletAdmissible ψHat}

namespace WaveletAdmissibilityPacket

/-- The profile projection of the native admissibility subtype. -/
abbrev ψHat (P : WaveletAdmissibilityPacket) : ℝ → ℂ :=
  P.1

/-- The admissibility witness carried by the native subtype. -/
abbrev admissible (P : WaveletAdmissibilityPacket) : waveletAdmissible P.ψHat :=
  P.2

/-- Recover the raw admissibility predicate from the packet. -/
theorem admissible_of_packet (P : WaveletAdmissibilityPacket) :
    waveletAdmissible P.ψHat :=
  P.admissible

end WaveletAdmissibilityPacket

namespace waveletAdmissible

variable {ψHat : ℝ → ℂ}

/--
Positive dilation preserves admissibility.

This is the native Mellin-scale transport law for the admissibility predicate.
-/
theorem comp_mul_left {a : ℝ} (ha : 0 < a) :
    waveletAdmissible (fun t => ψHat (a * t)) ↔ waveletAdmissible ψHat := by
  change
    MellinConvergent (fun t : ℝ => ((‖ψHat (a * t)‖ ^ 2 : ℝ) : ℂ)) 0 ↔
      waveletAdmissible ψHat
  simpa [waveletAdmissible, waveletEnergyDensity] using
    (MellinConvergent.comp_mul_left
      (f := waveletEnergyDensity ψHat) (s := (0 : ℂ)) (a := a) ha)

/--
Admissibility is invariant under a positive exponential dilation.

This is the form most directly tied to the logarithmic cylinder coordinate.
-/
theorem comp_exp (τ : ℝ) :
    waveletAdmissible (fun t => ψHat (Real.exp τ * t)) ↔ waveletAdmissible ψHat := by
  simpa using comp_mul_left (ψHat := ψHat) (a := Real.exp τ) (Real.exp_pos τ)

end waveletAdmissible

end InfoGeometry.Analysis.WaveletAdmissibilityCondition
