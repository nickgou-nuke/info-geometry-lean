import Mathlib
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# RestoreMonodromyTrace

Small sandbox packet for the Hadjiivanov monodromy trace/phase readout.
-/

namespace InfoGeometry.Restore.MonodromyTrace

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- The Bost-Connes spectrum of conformal weights. -/
noncomputable def conformalWeight (β : ℂ) (n : ℕ) : ℂ :=
  - (Complex.I * β * Real.log (n : ℝ)) / (2 * Real.pi)

/-- The monodromy trace is twice the phase. -/
theorem hadjiivanovMonodromy_trace (h : ℂ) :
    (hadjiivanovMonodromy h).trace = 2 * lcftPhase h := by
  simp [hadjiivanovMonodromy, upperJordan, Matrix.trace_fin_two]
  ring

/-- Trace of the monodromy block at the conformal weight. -/
theorem trace_hadjiivanovMonodromy_conformalWeight (β : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy (conformalWeight β n)).trace =
      2 * Complex.exp (- β * Real.log (n : ℝ)) := by
  rw [hadjiivanovMonodromy_trace]
  dsimp [lcftPhase, conformalWeight]
  congr 1
  have h_arg : -(2 : ℂ) * Complex.I * ↑Real.pi *
      (-(Complex.I * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi)) =
      -β * ↑(Real.log ↑n) := by
    calc
      -(2 : ℂ) * Complex.I * ↑Real.pi *
          (-(Complex.I * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi))
          = (-(2 : ℂ) * Complex.I * ↑Real.pi *
              -(Complex.I * β * ↑(Real.log ↑n))) / (2 * ↑Real.pi) := by ring
      _ = (2 * ↑Real.pi * (Complex.I * Complex.I) * β * ↑(Real.log ↑n)) /
          (2 * ↑Real.pi) := by ring
      _ = (2 * ↑Real.pi * (-1) * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi) := by
        rw [Complex.I_mul_I]
      _ = (-(2 * ↑Real.pi) * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi) := by ring
      _ = (-β * ↑(Real.log ↑n)) * (2 * ↑Real.pi) / (2 * ↑Real.pi) := by ring
      _ = -β * ↑(Real.log ↑n) := by
        rw [mul_div_cancel_right₀]
        have hpi : (Real.pi : ℂ) ≠ 0 := by
          exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        intro h_zero
        have h2 : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
        exact h2 h_zero
  rw [h_arg]

/-- Normalized trace gives the Dirichlet term. -/
theorem normalized_trace_eq_dirichlet_term (β : ℂ) (n : ℕ) :
    (1 / 2 : ℂ) * (hadjiivanovMonodromy (conformalWeight β n)).trace =
      Complex.exp (- β * Real.log (n : ℝ)) := by
  rw [trace_hadjiivanovMonodromy_conformalWeight]
  ring

end InfoGeometry.Restore.MonodromyTrace
