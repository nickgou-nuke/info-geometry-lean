import Mathlib
import proofs.TransferMatrixScattering

/-!
# Photonic Hardware Layout

A finite matrix model for the KAN photonic chip:

* `MZIBlock θ` realizes the compact rotation `K(θ)`;
* `GainLossBlock α` realizes the hyperbolic boost `A(α)`;
* `NilpotentDefectBlock γ` realizes the shear/EP throat `N(γ)`;
* one hardware cell realizes the transfer matrix `K A N`;
* every cell has determinant one, hence the extracted two-port scattering matrix
  has reciprocal transmission.
-/

noncomputable section

open Matrix Real

namespace InfoGeometry.GrandUnification.PhotonicHardwareLayout

open InfoGeometry.GrandUnification.TransferMatrixScattering

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Compact MZI rotation block. -/
def MZIBlock (θ : ℝ) : M2R :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Balanced gain/loss block. -/
def GainLossBlock (α : ℝ) : M2R :=
  !![Real.exp α, 0; 0, Real.exp (-α)]

/-- Nilpotent/EP throat shear block. -/
def NilpotentDefectBlock (γ : ℝ) : M2R :=
  !![1, γ; 0, 1]

/-- One physical KAN hardware cell. -/
def hardwareCell (θ α γ : ℝ) : M2R :=
  MZIBlock θ * GainLossBlock α * NilpotentDefectBlock γ

/-- Explicit hardware cell equals the KAN transfer matrix already used for scattering. -/
theorem hardwareCell_eq_transferM (θ α γ : ℝ) :
    hardwareCell θ α γ = transferM θ α γ := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [hardwareCell, MZIBlock, GainLossBlock, NilpotentDefectBlock, transferM]
      ring
    · simp [hardwareCell, MZIBlock, GainLossBlock, NilpotentDefectBlock, transferM]
      ring
  · fin_cases j
    · simp [hardwareCell, MZIBlock, GainLossBlock, NilpotentDefectBlock, transferM]
      ring
    · simp [hardwareCell, MZIBlock, GainLossBlock, NilpotentDefectBlock, transferM]
      ring

/-- MZI block is determinant-one. -/
theorem MZIBlock_det (θ : ℝ) : (MZIBlock θ).det = 1 := by
  simp [MZIBlock, Matrix.det_fin_two]
  rw [← pow_two, ← pow_two]
  exact Real.cos_sq_add_sin_sq θ

/-- Gain/loss block is determinant-one: balanced gain and loss. -/
theorem GainLossBlock_det (α : ℝ) : (GainLossBlock α).det = 1 := by
  simp [GainLossBlock, Matrix.det_fin_two]
  rw [← Real.exp_add]
  simp

/-- Nilpotent defect/shear block is determinant-one. -/
theorem NilpotentDefectBlock_det (γ : ℝ) : (NilpotentDefectBlock γ).det = 1 := by
  simp [NilpotentDefectBlock, Matrix.det_fin_two]

/-- Each physical KAN cell lies in `SL(2,R)`. -/
theorem hardwareCell_det (θ α γ : ℝ) :
    (hardwareCell θ α γ).det = 1 := by
  rw [hardwareCell_eq_transferM]
  exact transferM_det θ α γ

/-- Laboratory consequence: a single determinant-one hardware cell has reciprocal transmission. -/
theorem hardwareCell_transmission_reciprocity (θ α γ : ℝ) :
    (scatteringFromTransfer (hardwareCell θ α γ)) 0 0 =
      (scatteringFromTransfer (hardwareCell θ α γ)) 1 1 := by
  exact scattering_transmissions_equal_of_det_one (hardwareCell_det θ α γ)

/-- Reflection asymmetry observable: difference between right and left reflection amplitudes. -/
def reflectionAsymmetry (θ α γ : ℝ) : ℝ :=
  rightReflection (hardwareCell θ α γ) - leftReflection (hardwareCell θ α γ)

/-- Explicit reflection asymmetry for one KAN hardware cell. -/
theorem reflectionAsymmetry_formula (θ α γ : ℝ) :
    reflectionAsymmetry θ α γ =
      (Real.exp α * Real.sin θ +
        (γ * Real.exp α * Real.cos θ - Real.exp (-α) * Real.sin θ)) /
        (γ * Real.exp α * Real.sin θ + Real.exp (-α) * Real.cos θ) := by
  rw [reflectionAsymmetry, hardwareCell_eq_transferM]
  have h := transferM_reflections θ α γ
  rw [h.1, h.2]
  ring

/-- Consolidated hardware layout theorem. -/
theorem photonic_hardware_layout_synthesis :
    (∀ θ α γ : ℝ, hardwareCell θ α γ = transferM θ α γ) ∧
    (∀ θ : ℝ, (MZIBlock θ).det = 1) ∧
    (∀ α : ℝ, (GainLossBlock α).det = 1) ∧
    (∀ γ : ℝ, (NilpotentDefectBlock γ).det = 1) ∧
    (∀ θ α γ : ℝ, (hardwareCell θ α γ).det = 1) ∧
    (∀ θ α γ : ℝ,
      (scatteringFromTransfer (hardwareCell θ α γ)) 0 0 =
        (scatteringFromTransfer (hardwareCell θ α γ)) 1 1) := by
  constructor
  · intro θ α γ
    simpa using hardwareCell_eq_transferM θ α γ
  constructor
  · intro θ
    simpa using MZIBlock_det θ
  constructor
  · intro α
    simpa using GainLossBlock_det α
  constructor
  · intro γ
    simpa using NilpotentDefectBlock_det γ
  constructor
  · intro θ α γ
    simpa using hardwareCell_det θ α γ
  · intro θ α γ
    simpa using hardwareCell_transmission_reciprocity θ α γ

end InfoGeometry.GrandUnification.PhotonicHardwareLayout
