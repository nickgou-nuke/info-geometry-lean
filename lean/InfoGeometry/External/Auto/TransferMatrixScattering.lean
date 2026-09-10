import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.Matrix2KANPauliChain

/-!
# KAN Transfer Matrix → non-Abelian connection → scattering matrix

For the local transfer matrix

`M(k,α,γ)=K(k) A(α) N(γ)`

we prove:

* `det M = 1`;
* the explicit `SL(2,R)` Berry/gauge connection has zero trace;
* the laboratory scattering matrix obtained from a transfer matrix has reciprocal
  transmission when `det M = 1`.
-/

noncomputable section

open Matrix Real

namespace InfoGeometry.GrandUnification.TransferMatrixScattering

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Local KAN transfer matrix `K(k) A(α) N(γ)`. -/
def transferM (k α γ : ℝ) : M2R :=
  !![Real.exp α * Real.cos k,
     γ * Real.exp α * Real.cos k - Real.exp (-α) * Real.sin k;
     Real.exp α * Real.sin k,
     γ * Real.exp α * Real.sin k + Real.exp (-α) * Real.cos k]

/-- The KAN transfer matrix has determinant one. -/
theorem transferM_det (k α γ : ℝ) :
    (transferM k α γ).det = 1 := by
  simp [transferM, Matrix.det_fin_two]
  have hexp : Real.exp α * Real.exp (-α) = 1 := by
    rw [← Real.exp_add]
    simp
  have htrig := Real.cos_sq_add_sin_sq k
  ring_nf at htrig ⊢
  nlinarith [hexp, htrig]

/-- Explicit non-Abelian `SL(2,R)` gauge/Berry connection from `M⁻¹ ∂ₖM`. -/
def berryConnection (α γ : ℝ) : M2R :=
  !![-γ * Real.exp (2 * α),
     -((γ ^ 2 * Real.exp (4 * α) + 1) * Real.exp (-2 * α));
     Real.exp (2 * α),
     γ * Real.exp (2 * α)]

/-- The Abelian/U(1) trace part of the connection vanishes identically. -/
theorem berryConnection_trace_zero (α γ : ℝ) :
    Matrix.trace (berryConnection α γ) = 0 := by
  simp [berryConnection, Matrix.trace]

/-- Matrix entries used for transfer-to-scattering conversion. -/
def m11 (M : M2R) : ℝ := M 0 0
def m12 (M : M2R) : ℝ := M 0 1
def m21 (M : M2R) : ℝ := M 1 0
def m22 (M : M2R) : ℝ := M 1 1

/-- Standard two-port scattering matrix extracted from a transfer matrix. -/
def scatteringFromTransfer (M : M2R) : M2R :=
  (1 / m22 M) • !![1, -m12 M; m21 M, M.det]

/-- Transmission from the left/right are equal when `det M = 1`. -/
theorem scattering_transmissions_equal_of_det_one {M : M2R} (hdet : M.det = 1) :
    (scatteringFromTransfer M) 0 0 = (scatteringFromTransfer M) 1 1 := by
  simp [scatteringFromTransfer, m22, hdet]

/-- Explicit scattering matrix for the KAN transfer block. -/
theorem scattering_transferM_formula (k α γ : ℝ) :
    scatteringFromTransfer (transferM k α γ) =
      (1 / (γ * Real.exp α * Real.sin k + Real.exp (-α) * Real.cos k)) •
        !![1,
           -(γ * Real.exp α * Real.cos k - Real.exp (-α) * Real.sin k);
           Real.exp α * Real.sin k,
           1] := by
  ext i j <;> fin_cases i <;> fin_cases j
  · simp [scatteringFromTransfer, transferM, m22]
  · simp [scatteringFromTransfer, transferM, m12, m22]
  · simp [scatteringFromTransfer, transferM, m21, m22]
  · have hdet := transferM_det k α γ
    simp [transferM, Matrix.det_fin_two] at hdet
    simp [scatteringFromTransfer, transferM, m22, hdet]

/-- Reflection amplitudes extracted from `S`. -/
def leftReflection (M : M2R) : ℝ := (scatteringFromTransfer M) 0 1
def rightReflection (M : M2R) : ℝ := (scatteringFromTransfer M) 1 0

def transmission (M : M2R) : ℝ := (scatteringFromTransfer M) 0 0

/-- The reflection amplitudes of the KAN scattering matrix. -/
theorem transferM_reflections (k α γ : ℝ) :
    leftReflection (transferM k α γ) =
      -(γ * Real.exp α * Real.cos k - Real.exp (-α) * Real.sin k) /
        (γ * Real.exp α * Real.sin k + Real.exp (-α) * Real.cos k) ∧
    rightReflection (transferM k α γ) =
      (Real.exp α * Real.sin k) /
        (γ * Real.exp α * Real.sin k + Real.exp (-α) * Real.cos k) := by
  constructor
  · simp [leftReflection, scatteringFromTransfer, transferM, m12, m22, div_eq_mul_inv]
    ring
  · simp [rightReflection, scatteringFromTransfer, transferM, m21, m22, div_eq_mul_inv]
    ring

/-- Consolidated package. -/
theorem transfer_matrix_scattering_synthesis :
    (∀ k α γ : ℝ, (transferM k α γ).det = 1) ∧
    (∀ α γ : ℝ, Matrix.trace (berryConnection α γ) = 0) ∧
    (∀ M : M2R, M.det = 1 → (scatteringFromTransfer M) 0 0 = (scatteringFromTransfer M) 1 1) ∧
    (∀ k α γ : ℝ, scatteringFromTransfer (transferM k α γ) =
      (1 / (γ * Real.exp α * Real.sin k + Real.exp (-α) * Real.cos k)) •
        !![1,
           -(γ * Real.exp α * Real.cos k - Real.exp (-α) * Real.sin k);
           Real.exp α * Real.sin k,
           1]) := by
  exact ⟨transferM_det, berryConnection_trace_zero,
    fun _ h => scattering_transmissions_equal_of_det_one h,
    scattering_transferM_formula⟩

end InfoGeometry.GrandUnification.TransferMatrixScattering
