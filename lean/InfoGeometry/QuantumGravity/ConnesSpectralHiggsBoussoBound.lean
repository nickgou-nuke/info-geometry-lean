/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Section 121: Finite Matrix and Scalar Inequality Identities

This module proves identities for a two-by-two matrix-coordinate record and
scalar polynomials over a commutative ring. It does not construct a spectral
triple, Hilbert-space Dirac operator, spectral action, Raychaudhuri differential
equation, light-sheet, or geometric entropy flux. The final inequality is only
an arithmetic consequence of two supplied segment bounds and a nonnegative
final-area parameter; the geometric hypotheses remain open closure debt.
-/

namespace InfoGeometry.QuantumGravity.ConnesBousso

variable {R : Type*} [CommRing R]

/-! ### 1. Finite Two-by-Two Matrix-Coordinate Record -/

@[ext]
structure SheetMatrixCoord2 (R : Type*) where
  d11 : R
  d12 : R
  d21 : R
  d22 : R
  deriving DecidableEq, Repr, Inhabited

namespace SheetMatrixCoord2

variable {R : Type*} [CommRing R]

def zeroOp : SheetMatrixCoord2 R := ⟨0, 0, 0, 0⟩

def sampleSheetMatrixCoord2Int : SheetMatrixCoord2 ℤ := ⟨3, 4, 4, -3⟩

theorem sampleSheetMatrixCoord2Int_ne_zero :
    sampleSheetMatrixCoord2Int ≠ zeroOp := by
  decide

def mul (A B : SheetMatrixCoord2 R) : SheetMatrixCoord2 R :=
  ⟨A.d11 * B.d11 + A.d12 * B.d21, A.d11 * B.d12 + A.d12 * B.d22,
   A.d21 * B.d11 + A.d22 * B.d21, A.d21 * B.d12 + A.d22 * B.d22⟩

def trace (A : SheetMatrixCoord2 R) : R :=
  A.d11 + A.d22

/-- Non-commutativity of `SheetMatrixCoord2.mul` over `ℤ`. -/
theorem sheetMatrixCoord2_mul_noncommutative :
    let A : SheetMatrixCoord2 ℤ := ⟨1, 1, 0, 1⟩
    let B : SheetMatrixCoord2 ℤ := ⟨1, 0, 1, 1⟩
    mul A B ≠ mul B A := by
  decide

/-- Finite matrix-coordinate construction with diagonal entries `D₀` and `-D₀`
and equal off-diagonal entries `ϕ`; no operator representation is provided. -/
def connesDiracMatrixModel (D₀ ϕ : R) : SheetMatrixCoord2 R :=
  ⟨D₀, ϕ, ϕ, -D₀⟩

/-- The square of the defined finite matrix has diagonal entries `D₀² + ϕ²`
and zero off-diagonal entries. -/
theorem finite_sheet_matrix_square (D₀ ϕ : R) :
    mul (connesDiracMatrixModel D₀ ϕ) (connesDiracMatrixModel D₀ ϕ) =
    ⟨D₀^2 + ϕ^2, 0, 0, D₀^2 + ϕ^2⟩ := by
  dsimp [mul, connesDiracMatrixModel]
  ext <;> ring

/-- Trace of the square of the finite matrix-coordinate model. -/
theorem finite_sheet_matrix_trace_square (D₀ ϕ : R) :
    trace (mul (connesDiracMatrixModel D₀ ϕ) (connesDiracMatrixModel D₀ ϕ)) = 2 * (D₀^2 + ϕ^2) := by
  rw [finite_sheet_matrix_square]
  dsimp [trace]
  ring

end SheetMatrixCoord2

/-! ### 2. Scalar Quartic Potential Identity -/

/-- Scalar quartic polynomial `λ (ϕ² - v²)²`; no spectral action is constructed. -/
def spectralHiggsPotential (lam_coupling v_vev ϕ : R) : R :=
  lam_coupling * (ϕ^2 - v_vev^2)^2

/-- The scalar quartic polynomial vanishes at `ϕ = ±v`. -/
theorem higgs_vacuum_minima_zero (lam_coupling v_vev : R) :
    spectralHiggsPotential lam_coupling v_vev v_vev = 0 ∧
    spectralHiggsPotential lam_coupling v_vev (-v_vev) = 0 := by
  dsimp [spectralHiggsPotential]
  constructor <;> ring

/-- The scalar quartic is nonnegative over a linearly ordered ring when its coupling is nonnegative. -/
theorem spectralHiggsPotential_nonneg [LinearOrder R] [IsStrictOrderedRing R]
    (lam_coupling v_vev ϕ : R) (h_lambda : 0 ≤ lam_coupling) :
    0 ≤ spectralHiggsPotential lam_coupling v_vev ϕ := by
  dsimp [spectralHiggsPotential]
  exact mul_nonneg h_lambda (sq_nonneg (ϕ^2 - v_vev^2))

/-! ### 3. Scalar Inequalities -/

/-- Scalar polynomial appearing as a doubled Raychaudhuri right-hand side.
This record does not encode a congruence, derivative, or light-sheet. -/
def raychaudhuriFocusingRate2 (θ σ eight_pi_G T_kk : R) : R :=
  - θ^2 - 2 * σ^2 - 2 * eight_pi_G * T_kk

/-- The defined scalar polynomial is nonpositive when the coefficient and source terms are nonnegative. -/
theorem raychaudhuri_scalar_rhs_nonpos [LinearOrder R] [IsStrictOrderedRing R]
    (θ σ eight_pi_G T_kk : R)
    (h_G : 0 ≤ eight_pi_G) (h_nec : 0 ≤ T_kk) :
    raychaudhuriFocusingRate2 θ σ eight_pi_G T_kk ≤ 0 := by
  dsimp [raychaudhuriFocusingRate2]
  have h1 : 0 ≤ θ^2 := sq_nonneg θ
  have h2 : 0 ≤ σ^2 := sq_nonneg σ
  have h3 : 0 ≤ eight_pi_G * T_kk := mul_nonneg h_G h_nec
  linarith

/-- Two-segment scalar inequality: given local bounds and a nonnegative remainder,
the sum of the scalar terms is bounded by the initial scalar area parameter. -/
theorem two_segment_scalar_bound_transitive [LinearOrder R] [IsStrictOrderedRing R]
    (four_G S₀₁ S₁₂ A₀ A₁ A₂ : R)
    (h_seg1 : four_G * S₀₁ ≤ A₀ - A₁)
    (h_seg2 : four_G * S₁₂ ≤ A₁ - A₂)
    (h_final_area_nonneg : 0 ≤ A₂) :
    four_G * (S₀₁ + S₁₂) ≤ A₀ := by
  have h_sum : four_G * (S₀₁ + S₁₂) = four_G * S₀₁ + four_G * S₁₂ := by ring
  linarith [h_seg1, h_seg2, h_final_area_nonneg]

end InfoGeometry.QuantumGravity.ConnesBousso
