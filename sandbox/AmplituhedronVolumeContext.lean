import Mathlib
import InfoGeometry.Clifford.LogCftMonodromy
import Mathlib.NumberTheory.LSeries.RiemannZeta

open InfoGeometry.Clifford.LogCftMonodromy
open Matrix

namespace InfoGeometry.Physics.AmplituhedronVolume

noncomputable section

/-- 
The Bost-Connes Spectrum of Conformal Weights.
We map the integers n ∈ ℕ⁺ into a logarithmic conformal weight.
-/
def conformalWeight (β : ℂ) (n : ℕ) : ℂ :=
  - (Complex.I * β * Real.log (n : ℝ)) / (2 * Real.pi)

/-- 
The trace of the Hadjiivanov monodromy block at this conformal weight
evaluates to exactly 2 * n^(-β).
-/
theorem trace_hadjiivanovMonodromy_conformalWeight (β : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy (conformalWeight β n)).trace = 2 * Complex.exp (- β * Real.log (n : ℝ)) := by
  have h_trace : (hadjiivanovMonodromy (conformalWeight β n)).trace = 2 * lcftPhase (conformalWeight β n) := by
    simp [hadjiivanovMonodromy, upperJordan, Matrix.trace_fin_two]
    ring
  rw [h_trace]
  dsimp [lcftPhase, conformalWeight]
  congr 1
  have h_arg : -(2 : ℂ) * Complex.I * ↑Real.pi * (-(Complex.I * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi)) = -β * ↑(Real.log ↑n) := by
    calc -(2 : ℂ) * Complex.I * ↑Real.pi * (-(Complex.I * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi))
      _ = (-(2 : ℂ) * Complex.I * ↑Real.pi * -(Complex.I * β * ↑(Real.log ↑n))) / (2 * ↑Real.pi) := by ring
      _ = (2 * ↑Real.pi * (Complex.I * Complex.I) * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi) := by ring
      _ = (2 * ↑Real.pi * (-1) * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi) := by rw [Complex.I_mul_I]
      _ = (-(2 * ↑Real.pi) * β * ↑(Real.log ↑n)) / (2 * ↑Real.pi) := by ring
      _ = (-β * ↑(Real.log ↑n)) * (2 * ↑Real.pi) / (2 * ↑Real.pi) := by ring
      _ = -β * ↑(Real.log ↑n) := by
        rw [mul_div_cancel_right₀]
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        intro h_zero
        have h2 : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
        exact h2 h_zero
  rw [h_arg]

/-- 
The normalized trace maps exactly to the Dirichlet series term.
-/
theorem normalized_trace_eq_dirichlet_term (β : ℂ) (n : ℕ) :
    (1 / 2 : ℂ) * (hadjiivanovMonodromy (conformalWeight β n)).trace = Complex.exp (- β * Real.log (n : ℝ)) := by
  rw [trace_hadjiivanovMonodromy_conformalWeight]
  ring

/--
The L-loop Amplituhedron volume (β = L) is defined as the normalized trace summation.
Z(β) = ∑ (n ∈ ℕ⁺), (1/2) Tr(M(h_n(β)))
-/
def amplituhedronVolume (β : ℂ) : ℂ :=
  ∑' (n : ℕ), (1 / 2 : ℂ) * (hadjiivanovMonodromy (conformalWeight β (n + 1))).trace

/--
This summation is formally equivalent to the Riemann Zeta function.
By the above trace theorem, this evaluates to ∑ (n+1)^(-β).
-/
theorem amplituhedronVolume_eq_zeta_sum (β : ℂ) :
    amplituhedronVolume β = ∑' (n : ℕ), Complex.exp (- β * Real.log (n + 1 : ℝ)) := by
  dsimp [amplituhedronVolume]
  congr 1
  ext n
  have h_term := normalized_trace_eq_dirichlet_term β (n + 1)
  have h_cast : Real.log (↑(n + 1) : ℝ) = Real.log (↑n + 1 : ℝ) := by push_cast; rfl
  rw [h_cast] at h_term
  exact h_term
-- Lemma 1: Simplify the complex summand to an inverse square
lemma exp_neg_two_log_eq_inv_sq (n : ℕ) :
    Complex.exp (-2 * Real.log (n + 1 : ℝ)) = ↑((1:ℝ) / ((n + 1 : ℝ) ^ 2)) := by
  have h_arg : (-2 : ℂ) * ↑(Real.log (n + 1 : ℝ)) = ↑((-2 : ℝ) * Real.log (n + 1 : ℝ)) := by push_cast; rfl
  rw [h_arg, ← Complex.ofReal_exp]
  have h_pos : 0 < (n + 1 : ℝ) := by positivity
  have h_pow : Real.exp ((-2 : ℝ) * Real.log (n + 1 : ℝ)) = (n + 1 : ℝ) ^ (-2 : ℝ) := by
    rw [mul_comm]
    exact (Real.rpow_def_of_pos h_pos (-2 : ℝ)).symm
  rw [h_pow]
  have h_pow_int : (n + 1 : ℝ) ^ (-2 : ℝ) = (n + 1 : ℝ) ^ (-2 : ℤ) := by norm_cast
  rw [h_pow_int]
  have h_zpow : (n + 1 : ℝ) ^ (-2 : ℤ) = (1:ℝ) / ((n + 1 : ℝ) ^ 2) := by
    rw [_root_.zpow_neg, _root_.zpow_two, inv_eq_one_div, sq]
  rw [h_zpow]

-- Lemma 2: Commute the complex coercion outside the infinite sum
lemma tsum_complex_cast_inv_sq :
    (∑' (n : ℕ), ↑((1:ℝ) / ((n + 1 : ℝ) ^ 2))) = (↑(∑' (n : ℕ), (1:ℝ) / ((n + 1 : ℝ) ^ 2)) : ℂ) := by
  norm_cast

-- Theorem 3: The final evaluation using Mathlib's Basel result
theorem amplituhedronVolume_two :
    amplituhedronVolume 2 = ↑((Real.pi ^ 2 / 6 : ℝ)) := by
  rw [amplituhedronVolume_eq_zeta_sum]
  have h_simp : (∑' (n : ℕ), Complex.exp (-2 * Real.log (n + 1 : ℝ))) = ∑' (n : ℕ), ↑((1:ℝ) / ((n + 1 : ℝ) ^ 2)) := by
    congr 1
    ext n
    exact exp_neg_two_log_eq_inv_sq n
  rw [h_simp, tsum_complex_cast_inv_sq]
  congr 1
  have h_basel := hasSum_zeta_two.tsum_eq
  rw [hasSum_zeta_two.summable.tsum_eq_zero_add] at h_basel
  have h_zero : (1 : ℝ) / (↑(0:ℕ) : ℝ) ^ 2 = 0 := by norm_num
  rw [h_zero, zero_add] at h_basel
  push_cast at h_basel
  rw [← h_basel]


end

end InfoGeometry.Physics.AmplituhedronVolume
