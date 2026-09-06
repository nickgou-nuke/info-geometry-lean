import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import InfoGeometry.Analysis.BipolarCriticalPhase
import InfoGeometry.Quantum.LoxodromicGauge
import InfoGeometry.OperatorAlgebra.AndreevBoundary
import Mathlib.Tactic

/-!
# Bipolar loxodromic and particle-hole involution bridge

This file separates two involutions that were conflated in an informal physics
narrative.

* The geometric reflection is `s ↦ 1 - conj(s)`. It flips the radial logarithm
  and preserves the angular phase at the multiplicative level:
  `q(mirror s) = conj(q s)⁻¹`.
* Particle-hole/Andreev phase conjugation is a different operation: it flips the
  channel and complex-conjugates its amplitude.

No time-reversal operator, BdG Hamiltonian, spectral gap, or superconducting
boundary condition is inferred from these finite algebraic identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarLoxodromicAndreevBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Quantum.LoxodromicGauge
open InfoGeometry.OperatorAlgebra.AndreevBoundary

/-- Loxodromic scalar reconstructed from the bipolar logarithmic coordinates. -/
def bipolarLoxodromic (s : ℂ) : ℂ :=
  loxodromicMap (eta s) (theta s)

/-- The bipolar loxodromic scalar is exactly the canonical Cayley coordinate. -/
theorem bipolarLoxodromic_eq_crossRatio01 {s : ℂ} (hs : s ∈ punctured01) :
    bipolarLoxodromic s = crossRatio01 s := by
  simpa [bipolarLoxodromic, loxodromicMap] using exp_eta_theta hs

/-- Its modulus is the exponential of the radial logarithmic coordinate. -/
theorem norm_bipolarLoxodromic (s : ℂ) :
    ‖bipolarLoxodromic s‖ = Real.exp (eta s) := by
  exact loxodromic_scale_factor (eta s) (theta s)

/-- The critical line is exactly the unit-modulus specialization of this scalar. -/
theorem bipolarLoxodromic_criticalLine_unit (y : ℝ) :
    ‖bipolarLoxodromic (criticalLine y)‖ = 1 := by
  rw [norm_bipolarLoxodromic, eta_criticalLine, Real.exp_zero]

/-- Reflection preserves the punctured domain. -/
theorem mirror_mem_punctured01 {s : ℂ} (hs : s ∈ punctured01) :
    mirror s ∈ punctured01 := by
  constructor
  · intro h0
    apply hs.2
    have hc : (starRingEnd ℂ) s = 1 := by
      calc
        (starRingEnd ℂ) s = 1 - mirror s := by simp [mirror]
        _ = 1 := by rw [h0]; ring
    have := congrArg (starRingEnd ℂ) hc
    simpa using this
  · intro h1
    apply hs.1
    have hc : (starRingEnd ℂ) s = 0 := by
      calc
        (starRingEnd ℂ) s = 1 - mirror s := by simp [mirror]
        _ = 0 := by rw [h1]; ring
    have := congrArg (starRingEnd ℂ) hc
    simpa using this

/-- Reflection sends the exact loxodromic/Cayley scalar to inverse conjugate. -/
theorem bipolarLoxodromic_mirror {s : ℂ} (hs : s ∈ punctured01) :
    bipolarLoxodromic (mirror s) =
      ((starRingEnd ℂ) (bipolarLoxodromic s))⁻¹ := by
  rw [bipolarLoxodromic_eq_crossRatio01 (mirror_mem_punctured01 hs),
    bipolarLoxodromic_eq_crossRatio01 hs, crossRatio01_mirror]

/-- Complex phase conjugation. This is distinct from geometric reflection. -/
def phaseConjugate (z : ℂ) : ℂ := (starRingEnd ℂ) z

@[simp] theorem phaseConjugate_involutive (z : ℂ) :
    phaseConjugate (phaseConjugate z) = z := by
  simp [phaseConjugate]

/-- On unit norm, phase conjugation is inversion. -/
theorem phaseConjugate_eq_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    phaseConjugate z = z⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  apply mul_left_cancel₀ hz0
  rw [mul_inv_cancel₀ hz0]
  simpa [Complex.star_def, Complex.normSq_eq_norm_sq, hz] using
    (Complex.mul_conj z)

/-- Complex Nambu-style amplitudes indexed by the repository-owned Andreev channels. -/
abbrev ComplexAndreevAmplitude := AndreevChannel → ℂ

/-- Anti-linear particle-hole phase flip: channel exchange plus complex conjugation. -/
def phaseAndreevFlip (ψ : ComplexAndreevAmplitude) : ComplexAndreevAmplitude :=
  fun c => (starRingEnd ℂ) (ψ (AndreevChannel.flip c))

/-- The phase-Andreev flip is involutive. -/
theorem phaseAndreevFlip_sq (ψ : ComplexAndreevAmplitude) :
    phaseAndreevFlip (phaseAndreevFlip ψ) = ψ := by
  funext c
  cases c <;> simp [phaseAndreevFlip]

/-- Critical-line phase pair: one channel carries the phase and the other its conjugate. -/
def criticalPhasePair (y : ℝ) : ComplexAndreevAmplitude
  | AndreevChannel.electronLike => criticalPhase y
  | AndreevChannel.holeLike => (starRingEnd ℂ) (criticalPhase y)

/-- The critical phase pair is fixed by the anti-linear particle-hole closure. -/
theorem criticalPhasePair_fixed (y : ℝ) :
    phaseAndreevFlip (criticalPhasePair y) = criticalPhasePair y := by
  funext c
  cases c <;> simp [phaseAndreevFlip, criticalPhasePair]

/-- Compact separation packet: geometric reflection and particle-hole conjugation are
both involutive structures, but they act differently. -/
theorem loxodromic_andreev_separation_packet
    {s : ℂ} (hs : s ∈ punctured01) (y : ℝ) :
    bipolarLoxodromic s = crossRatio01 s ∧
      bipolarLoxodromic (mirror s) = ((starRingEnd ℂ) (bipolarLoxodromic s))⁻¹ ∧
      ‖bipolarLoxodromic (criticalLine y)‖ = 1 ∧
      phaseAndreevFlip (criticalPhasePair y) = criticalPhasePair y := by
  exact ⟨bipolarLoxodromic_eq_crossRatio01 hs,
    bipolarLoxodromic_mirror hs,
    bipolarLoxodromic_criticalLine_unit y,
    criticalPhasePair_fixed y⟩

end InfoGeometry.Canonical.BipolarLoxodromicAndreevBridge
