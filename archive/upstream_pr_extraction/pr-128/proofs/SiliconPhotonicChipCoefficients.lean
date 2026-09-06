import Mathlib
import proofs.NonHermitianSMatrixDefect

/-!
# Silicon Photonic Chip Coefficients for the Hyperbolic Braid Gate

A finite engineering-level coefficient layer for the non-Hermitian/J-unitary
`2 × 2` scattering block.  With interaction strength `α = κ L`, the amplitudes
are

`t(α) = cosh α`, `r(α) = sinh α`.

Thus the ordinary intensity budget has gain `T+R`, while the Krein/SU(1,1) flux
balance is exactly `T-R=1`.
-/

noncomputable section

open Real

namespace InfoGeometry.GrandUnification.SiliconPhotonicChipCoefficients

/-- Coupling-length interaction strength `α = κL`. -/
def interactionStrength (coupling length : ℝ) : ℝ :=
  coupling * length

/-- Transmission amplitude of the hyperbolic chip gate. -/
def transmissionAmplitude (α : ℝ) : ℝ :=
  Real.cosh α

/-- Reflection/cross-port amplitude of the hyperbolic chip gate. -/
def reflectionAmplitude (α : ℝ) : ℝ :=
  Real.sinh α

/-- Transmission intensity. -/
def transmittance (α : ℝ) : ℝ :=
  transmissionAmplitude α ^ 2

/-- Reflection intensity. -/
def reflectance (α : ℝ) : ℝ :=
  reflectionAmplitude α ^ 2

/-- Euclidean intensity gain/loss budget. -/
def euclideanIntensityBudget (α : ℝ) : ℝ :=
  transmittance α + reflectance α

/-- Nonunitary excess over ordinary unitary intensity conservation. -/
def euclideanIntensityDefect (α : ℝ) : ℝ :=
  euclideanIntensityBudget α - 1

/-- Exceptional-point gain/loss contrast for a balanced two-waveguide coupler. -/
def epGainLossContrast (coupling : ℝ) : ℝ :=
  2 * coupling

/-- `α = κL` by definition. -/
theorem interactionStrength_eq (κ L : ℝ) :
    interactionStrength κ L = κ * L := rfl

/-- At the balanced EP, `Δγ = 2κ`, equivalently `κ = Δγ/2`. -/
theorem epGainLossContrast_halves (κ : ℝ) :
    epGainLossContrast κ / 2 = κ := by
  simp [epGainLossContrast]

/-- Krein/SU(1,1) flux balance: `T - R = 1`. -/
theorem krein_intensity_balance (α : ℝ) :
    transmittance α - reflectance α = 1 := by
  simpa [transmittance, reflectance, transmissionAmplitude, reflectionAmplitude]
    using Real.cosh_sq_sub_sinh_sq α

/-- The Euclidean budget is `cosh² α + sinh² α`. -/
theorem euclideanIntensityBudget_formula (α : ℝ) :
    euclideanIntensityBudget α = Real.cosh α ^ 2 + Real.sinh α ^ 2 := by
  rfl

/-- The ordinary nonunitary excess is exactly `2 sinh² α`. -/
theorem euclideanIntensityDefect_formula (α : ℝ) :
    euclideanIntensityDefect α = 2 * Real.sinh α ^ 2 := by
  unfold euclideanIntensityDefect euclideanIntensityBudget transmittance reflectance
    transmissionAmplitude reflectionAmplitude
  have h := Real.cosh_sq_sub_sinh_sq α
  nlinarith

/-- Coefficients after substituting the chip interaction strength `α=κL`. -/
theorem chip_coefficients_from_coupling_length (κ L : ℝ) :
    transmissionAmplitude (interactionStrength κ L) = Real.cosh (κ * L) ∧
    reflectionAmplitude (interactionStrength κ L) = Real.sinh (κ * L) ∧
    transmittance (interactionStrength κ L) - reflectance (interactionStrength κ L) = 1 ∧
    euclideanIntensityDefect (interactionStrength κ L) = 2 * Real.sinh (κ * L) ^ 2 := by
  exact ⟨rfl, rfl, krein_intensity_balance (κ * L), euclideanIntensityDefect_formula (κ * L)⟩

/-- Consolidated chip coefficient package. -/
theorem silicon_photonic_chip_coefficients_synthesis :
    (∀ κ L : ℝ, interactionStrength κ L = κ * L) ∧
    (∀ κ : ℝ, epGainLossContrast κ / 2 = κ) ∧
    (∀ α : ℝ, transmittance α - reflectance α = 1) ∧
    (∀ α : ℝ, euclideanIntensityDefect α = 2 * Real.sinh α ^ 2) ∧
    (∀ κ L : ℝ,
      transmissionAmplitude (interactionStrength κ L) = Real.cosh (κ * L) ∧
      reflectionAmplitude (interactionStrength κ L) = Real.sinh (κ * L) ∧
      transmittance (interactionStrength κ L) - reflectance (interactionStrength κ L) = 1 ∧
      euclideanIntensityDefect (interactionStrength κ L) = 2 * Real.sinh (κ * L) ^ 2) := by
  exact ⟨interactionStrength_eq, epGainLossContrast_halves, krein_intensity_balance,
    euclideanIntensityDefect_formula, chip_coefficients_from_coupling_length⟩

end InfoGeometry.GrandUnification.SiliconPhotonicChipCoefficients
