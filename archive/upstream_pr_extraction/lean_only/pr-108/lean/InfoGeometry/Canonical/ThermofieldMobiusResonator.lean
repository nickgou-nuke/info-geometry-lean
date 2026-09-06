import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
import InfoGeometry.Canonical.ThermofieldBidirectionalResonator

/-!
# ThermofieldMöbiusResonator

A lossy Möbius resonator on the projectivization of a doubled thermofield/chiral carrier.

This file formalizes the dynamical system described by two counterpropagating
amplitudes with bidirectional coupling, decay, and thermal weighting.
The round-trip dynamics induces a Möbius transformation on the projective ratio.
-/

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldMobiusResonator

open Complex
open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
open InfoGeometry.Canonical.ThermofieldBidirectionalResonator

/-!
=============================================================================
PART 1: Twin Amplitude Carrier
=============================================================================
-/

/-- Relative density ρ_rel = |z|² -/
def relativeDensity (ψ : TwinAmplitude) : ℝ :=
  Complex.normSq (projectiveRatio ψ)

/-- Relative surprisal -/
def relativeSurprisal (ψ : TwinAmplitude) : ℝ :=
  -Real.log (relativeDensity ψ)

/-- Madelung-like coordinates: (relativeSurprisal, arg z) -/
def madelungCoordinates (ψ : TwinAmplitude) : ℝ × ℝ :=
  (relativeSurprisal ψ, Complex.arg (projectiveRatio ψ))

/-!
=============================================================================
PART 2: Continuous Dynamics (Coupled System)
=============================================================================
-/

/-- Symmetric case solution: a₊(t) = e^{-(γ+iω)t} cos(gt), a₋(t) = -i e^{-(γ+iω)t} sin(gt) -/
def symmetricSolution (γ ω g : ℝ) (t : ℝ) : TwinAmplitude :=
  let phase := Complex.exp (-(γ + Complex.I * ω) * t)
  ⟨phase * Real.cos (g * t),
   -Complex.I * phase * Real.sin (g * t)⟩

/-!
=============================================================================
PART 3: Discrete Round-Trip Dynamics
=============================================================================
-/

/-- Transfer matrix for one round trip: M = R ∘ P -/
structure RoundTripMatrix where
  A : ℂ
  B : ℂ
  C : ℂ
  D : ℂ
  detCondition : A * D - B * C = 1  -- Normalized for Möbius action

/-- Round-trip action on amplitudes: Ψ ↦ M Ψ -/
def roundTripAct (M : RoundTripMatrix) (ψ : TwinAmplitude) : TwinAmplitude :=
  ⟨M.A * ψ.aPlus + M.B * ψ.aMinus,
   M.C * ψ.aPlus + M.D * ψ.aMinus⟩

/-- Möbius transformation on the projective ratio: z ↦ (C + D z) / (A + B z) -/
def mobiusAction (M : RoundTripMatrix) (z : ℂ) : ℂ :=
  (M.C + M.D * z) / (M.A + M.B * z)

/-- Compatibility: projectiveRatio (M Ψ) = mobiusAction M (projectiveRatio ψ) -/
theorem mobiusCompatibility (M : RoundTripMatrix) (ψ : TwinAmplitude)
    (ha : ψ.aPlus ≠ 0) :
    projectiveRatio (roundTripAct M ψ) = mobiusAction M (projectiveRatio ψ) := by
  unfold projectiveRatio roundTripAct mobiusAction
  have h_num : M.C * ψ.aPlus + M.D * ψ.aMinus = (M.C + M.D * (ψ.aMinus / ψ.aPlus)) * ψ.aPlus := by
    calc M.C * ψ.aPlus + M.D * ψ.aMinus
      _ = M.C * ψ.aPlus + M.D * (ψ.aMinus / ψ.aPlus * ψ.aPlus) := by rw [div_mul_cancel₀ _ ha]
      _ = (M.C + M.D * (ψ.aMinus / ψ.aPlus)) * ψ.aPlus := by ring
  have h_den : M.A * ψ.aPlus + M.B * ψ.aMinus = (M.A + M.B * (ψ.aMinus / ψ.aPlus)) * ψ.aPlus := by
    calc M.A * ψ.aPlus + M.B * ψ.aMinus
      _ = M.A * ψ.aPlus + M.B * (ψ.aMinus / ψ.aPlus * ψ.aPlus) := by rw [div_mul_cancel₀ _ ha]
      _ = (M.A + M.B * (ψ.aMinus / ψ.aPlus)) * ψ.aPlus := by ring
  rw [h_num, h_den, mul_div_mul_right _ _ ha]

/-!
=============================================================================
PART 4: Thermofield Bridge
=============================================================================
-/

/-- Thermal weight factor e^{-βE/2} -/
def thermalWeight (β E : ℝ) : ℝ :=
  Real.exp (-β * E / 2)

/-- Full amplitude with thermal, decay, phase, and coupling factors:
    a₊(t) ~ e^{-βE/2} e^{-γt} e^{-iωt} cos(gt)
    a₋(t) ~ e^{-βE/2} e^{-γt} e^{-iωt} sin(gt) -/
def thermofieldAmplitude (β E γ ω g t : ℝ) : TwinAmplitude :=
  let envelope := thermalWeight β E * Real.exp (-γ * t)
  let phase := Complex.exp (-Complex.I * ω * t)
  ⟨envelope * phase * Real.cos (g * t),
   -Complex.I * envelope * phase * Real.sin (g * t)⟩

/-- The envelope decays as e^{-2γt} independently of the thermal weight -/
theorem envelopeDecay (β E γ ω g t : ℝ) :
    totalEnergy (thermofieldAmplitude β E γ ω g t) =
      (thermalWeight β E) ^ 2 * Real.exp (-2 * γ * t) := by
  unfold totalEnergy energyPlus energyMinus thermofieldAmplitude
  dsimp
  have h_phase : Complex.normSq (Complex.exp (-Complex.I * ω * t)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    have : (-Complex.I * ω * t).re = 0 := by simp
    rw [this, Real.exp_zero, one_pow]
  have h_plus : Complex.normSq ((thermalWeight β E : ℂ) * (Real.exp (-γ * t) : ℂ) * Complex.exp (-Complex.I * ω * t) * (Real.cos (g * t) : ℂ)) =
      (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * (Real.cos (g * t)) ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, h_phase, mul_one, Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  have h_minus : Complex.normSq (-Complex.I * (thermalWeight β E : ℂ) * (Real.exp (-γ * t) : ℂ) * Complex.exp (-Complex.I * ω * t) * (Real.sin (g * t) : ℂ)) =
      (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * (Real.sin (g * t)) ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, h_phase, mul_one, Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  simp_rw [Complex.ofReal_mul, ← mul_assoc (-Complex.I)]
  rw [h_plus, h_minus]
  have h_trig : (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * (Real.cos (g * t)) ^ 2 +
                (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * (Real.sin (g * t)) ^ 2 =
                (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 := by
    calc (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * (Real.cos (g * t)) ^ 2 +
         (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * (Real.sin (g * t)) ^ 2
      _ = (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * ((Real.cos (g * t)) ^ 2 + (Real.sin (g * t)) ^ 2) := by ring
      _ = (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq]
      _ = (thermalWeight β E) ^ 2 * (Real.exp (-γ * t)) ^ 2 := mul_one _
  rw [h_trig]
  have h_exp : (Real.exp (-γ * t)) ^ 2 = Real.exp (-2 * γ * t) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [h_exp]

/-!
=============================================================================
PART 5: Connection to Split-Octonion Peirce Frame
=============================================================================
-/

/-- Embed a TwinAmplitude into the split-octonion Peirce frame -/
def embedToPeirceFrame (ψ : TwinAmplitude) : ZornMatrix ℝ :=
  ⟨ψ.aPlus.re,
   ψ.aMinus.re,
   ![ψ.aPlus.im, 0, 0],
   ![ψ.aMinus.im, 0, 0]⟩

/-- The Peirce projectors recover the amplitudes -/
theorem peirceRecoversAmplitudes (ψ : TwinAmplitude) :
    (embedToPeirceFrame ψ).a = ψ.aPlus.re ∧
    (embedToPeirceFrame ψ).b = ψ.aMinus.re := by
  exact ⟨rfl, rfl⟩

end InfoGeometry.Canonical.ThermofieldMobiusResonator
