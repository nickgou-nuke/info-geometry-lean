import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge
import Mathlib.Tactic

namespace InfoGeometry.Canonical

open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

/-- Polarized basis indices for the 4×4 matrix units in each coloured core:
0 = n₊ (E₁₁), 1 = n₋ (E₂₂), 2 = σ₊ (E₁₂), 3 = σ₋ (E₂₁) -/
inductive PolarizedBasisIdx where
  | nPlus : PolarizedBasisIdx
  | nMinus : PolarizedBasisIdx
  | sigmaPlus : PolarizedBasisIdx
  | sigmaMinus : PolarizedBasisIdx
deriving DecidableEq, Fintype

/-- Convert Fin 4 to PolarizedBasisIdx -/
def finToPolarized (i : Fin 4) : PolarizedBasisIdx :=
  match i with
  | ⟨0, _⟩ => .nPlus
  | ⟨1, _⟩ => .nMinus
  | ⟨2, _⟩ => .sigmaPlus
  | ⟨3, _⟩ => .sigmaMinus

/-- The polarized basis elements for a fixed colour -/
def polarizedBasis (c : SplitOctonionColour) : PolarizedBasisIdx → StandardRationalSplitOctonion
  | .nPlus => modularNPlus
  | .nMinus => modularNMinus
  | .sigmaPlus => modularSigmaPlus c
  | .sigmaMinus => modularSigmaMinus c

/-- Polarized multiplication table: (a, b) ↦ coefficient of c in a*b
This is the 4×4 matrix unit multiplication:
n₊² = n₊, n₋² = n₋, n₊n₋ = n₋n₊ = 0
σ₊² = σ₋² = 0
σ₊σ₋ = n₊, σ₋σ₊ = n₋
n₊σ₊ = σ₊, σ₊n₋ = σ₊
n₋σ₋ = σ₋, σ₋n₊ = σ₋
n₊σ₋ = σ₊n₊ = n₋σ₊ = σ₋n₋ = 0 -/
def polarizedMulCoeff (a b c : PolarizedBasisIdx) : ℚ :=
  match a, b, c with
  | .nPlus, .nPlus, .nPlus => 1
  | .nMinus, .nMinus, .nMinus => 1
  | .sigmaPlus, .sigmaMinus, .nPlus => 1
  | .sigmaMinus, .sigmaPlus, .nMinus => 1
  | .nPlus, .sigmaPlus, .sigmaPlus => 1
  | .sigmaPlus, .nMinus, .sigmaPlus => 1
  | .nMinus, .sigmaMinus, .sigmaMinus => 1
  | .sigmaMinus, .nPlus, .sigmaMinus => 1
  | _, _, _ => 0

/-- Compute the product of two polarized basis elements in the polarized basis -/
def polarizedMul (c : SplitOctonionColour) (a b : PolarizedBasisIdx) : StandardRationalSplitOctonion :=
  ∑ k : PolarizedBasisIdx, (polarizedMulCoeff a b k : ℚ) • polarizedBasis c k

/-- Verify that polarizedMul agrees with the actual split-octonion multiplication -/
theorem polarizedMul_correct (c : SplitOctonionColour) (a b : PolarizedBasisIdx) :
    polarizedMul c a b = splitOctonionMulQ (polarizedBasis c a) (polarizedBasis c b) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> native_decide

/-- The 4×4 matrix of multiplication coefficients for a fixed colour -/
def polarizedMultiplicationMatrix (c : SplitOctonionColour) : Matrix (Fin 4) (Fin 4) (ℚ) :=
  fun i j => ∑ k : Fin 4, (polarizedMulCoeff (finToPolarized i) (finToPolarized j) (finToPolarized k) : ℚ)

/-- The polarized basis forms a complete set of matrix units for M₂(ℚ) -/
theorem polarizedBasis_isMatrixUnits (c : SplitOctonionColour) :
    ∀ (a b : PolarizedBasisIdx),
    splitOctonionMulQ (polarizedBasis c a) (polarizedBasis c b) =
      ∑ k : PolarizedBasisIdx, (polarizedMulCoeff a b k : ℚ) • polarizedBasis c k := by
  intro a b
  have h := polarizedMul_correct c a b
  simp [polarizedMul] at h ⊢
  <;> rw [h]
  <;> simp [polarizedMul]

end
end InfoGeometry.Canonical
