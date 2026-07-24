import Mathlib

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.LogJordanKreinCore

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Nilpotent Jordan Block N = (0 1; 0 0) -/
def N : M2R := !![0, 1; 0, 0]

/-- 2D Jordan Cell Operator L_Δ = Δ I + N = (Δ 1; 0 Δ) -/
def L0 (Delta : ℝ) : M2R := !![Delta, 1; 0, Delta]

/-- Krein Signature Matrix G = (0 1; 1 0) -/
def kreinG : M2R := !![0, 1; 1, 0]

/-- One-Mode Parity Involution χ = (1 0; 0 -1) -/
def parity : M2R := !![1, 0; 0, -1]

/-- Theorem 1: N is strictly nilpotent: N² = 0 -/
theorem jordanNilpotent_sq : N * N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Theorem 2: N is non-zero -/
theorem jordanNilpotent_ne_zero : N ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [N] at h01

/-- Theorem 3: Jordan Cell is Krein Self-Adjoint: L_Δᵀ G = G L_Δ -/
theorem jordanCell_krein_selfAdjoint (Delta : ℝ) :
    (L0 Delta).transpose * kreinG = kreinG * L0 Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L0, kreinG, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- Time evolution matrix exponential for 2D Jordan Cell: E(t, Δ) = e^{t Δ} (I + t N) -/
def expJordanCell (t Delta : ℝ) : M2R :=
  Real.exp (t * Delta) • (1 + t • N)

/-- Explicit Matrix Form of expJordanCell -/
theorem expJordanCell_explicit (t Delta : ℝ) :
    expJordanCell t Delta = !![Real.exp (t * Delta), t * Real.exp (t * Delta); 0, Real.exp (t * Delta)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expJordanCell, N, Matrix.smul_apply, Matrix.add_apply, mul_comm]

/-- Theorem 4: Ordinary Trace of Jordan Cell Evolution: Tr(e^{t L_Δ}) = 2 e^{t Δ} -/
theorem trace_exp_jordanCell (t Delta : ℝ) :
    Matrix.trace (expJordanCell t Delta) = 2 * Real.exp (t * Delta) := by
  rw [expJordanCell_explicit]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- Theorem 5: Detector Trace using Nᵀ: Tr(Nᵀ e^{t L_Δ}) = t e^{t Δ} (Extracts Jordan Logarithmic Coefficient) -/
theorem detector_trace_jordanCell (t Delta : ℝ) :
    Matrix.trace (N.transpose * expJordanCell t Delta) = t * Real.exp (t * Delta) := by
  rw [expJordanCell_explicit]
  simp [N, Matrix.transpose_apply, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Theorem 6: Parity Supertrace of Jordan Cell Evolution: Tr(χ e^{t L_Δ}) = 0 -/
theorem parity_trace_jordanCell (t Delta : ℝ) :
    Matrix.trace (parity * expJordanCell t Delta) = 0 := by
  rw [expJordanCell_explicit]
  simp [parity, Matrix.trace, Fin.sum_univ_two]

/-- Certified Logarithmic Jordan-Krein Apex Packet -/
structure LogJordanKreinPacket where
  nilpotent_sq : N * N = 0
  nilpotent_nz : N ≠ 0
  krein_self_adjoint : ∀ Delta, (L0 Delta).transpose * kreinG = kreinG * L0 Delta
  trace_val : ∀ t Delta, Matrix.trace (expJordanCell t Delta) = 2 * Real.exp (t * Delta)
  detector_val : ∀ t Delta, Matrix.trace (N.transpose * expJordanCell t Delta) = t * Real.exp (t * Delta)
  parity_val : ∀ t Delta, Matrix.trace (parity * expJordanCell t Delta) = 0

theorem log_jordan_krein_apex_exists : Nonempty LogJordanKreinPacket :=
  ⟨⟨jordanNilpotent_sq, jordanNilpotent_ne_zero, jordanCell_krein_selfAdjoint,
    trace_exp_jordanCell, detector_trace_jordanCell, parity_trace_jordanCell⟩⟩

end InfoGeometry.Canonical.LogJordanKreinCore