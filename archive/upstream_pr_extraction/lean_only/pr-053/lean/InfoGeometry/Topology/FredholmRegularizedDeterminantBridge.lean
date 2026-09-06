import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Finite Regularized Factor and Affine Spectral Readouts

This module formalizes only the elementary one-mode primary factor associated
with a proposed order-2 Fredholm determinant.  It does not define an operator,
an infinite determinant, or a Hilbert--Pólya realization.

1. **Regularized Fredholm Determinant Factor ($\det_2$):**
   - For a real eigenvalue $\lambda \in \mathbb{R}^*$:
     $$E_2(w, \lambda) = (1 - w \lambda) e^{w \lambda}$$
   - The exponential factor $e^{w \lambda}$ ensures convergence for Hilbert-Schmidt operators ($\sum \lambda_n^2 < \infty$).

2. **Spectral Zero Locus Theorem:**
   - Because $e^{w \lambda} \ne 0$ for all $w \in \mathbb{C}$:
     $$E_2(w, \lambda) = 0 \iff 1 - w \lambda = 0 \iff w = \frac{1}{\lambda} \in \mathbb{R}$$
   - The proved zero statement is only for the displayed single-mode factor;
     no infinite spectral zero set is constructed.

3. **Affine-coordinate firewall:**
   - A real zero of the centered variable gives only
     $$\operatorname{Re}(w+1/2)=1/2+\operatorname{Re}(w).$$
   - Hence real spectral zeros do not by themselves imply the Riemann critical
     line.  In centered coordinates the critical-line condition is
     $\operatorname{Re}(w)=0$, a separate hypothesis.

All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Topology.FredholmRegularizedDeterminantBridge

open Complex

/-! ### 1. Genus-2 Regularized Fredholm Factor -/

/-- Single-mode genus-2 regularized Fredholm factor E₂(w, λ) = (1 - w * λ) * exp(w * λ) -/
def fredholmFactor2 (w : ℂ) (lambda : ℝ) : ℂ :=
  (1 - w * (lambda : ℂ)) * Complex.exp (w * (lambda : ℂ))

/-- 🏆 THEOREM 1: The exponential regulator is non-vanishing everywhere -/
theorem fredholm_regulator_nonvanishing (w : ℂ) (lambda : ℝ) :
    Complex.exp (w * (lambda : ℂ)) ≠ 0 :=
  Complex.exp_ne_zero (w * (lambda : ℂ))

/-- 🏆 THEOREM 2: Exact Zero Locus of the Regularized Factor -/
theorem fredholmFactor2_zero_iff (w : ℂ) (lambda : ℝ) (hlam : lambda ≠ 0) :
    fredholmFactor2 w lambda = 0 ↔ w = (1 / (lambda : ℂ)) := by
  dsimp [fredholmFactor2]
  have h_exp := fredholm_regulator_nonvanishing w lambda
  have h_lam_c : (lambda : ℂ) ≠ 0 := by exact_mod_cast hlam
  constructor
  · intro h
    cases mul_eq_zero.mp h with
    | inl h_lin =>
      have h1 : 1 - w * (lambda : ℂ) = 0 := h_lin
      have h2 : w * (lambda : ℂ) = 1 := by
        calc
          w * (lambda : ℂ) = 1 - (1 - w * (lambda : ℂ)) := by ring
          _ = 1 - 0 := by rw [h1]
          _ = 1 := by ring
      calc
        w = (w * (lambda : ℂ)) / (lambda : ℂ) := by rw [mul_div_cancel_right₀ w h_lam_c]
        _ = 1 / (lambda : ℂ) := by rw [h2]
    | inr h_exp_zero => exact False.elim (h_exp h_exp_zero)
  · intro hw
    rw [hw]
    have h_cancel : (1 / (lambda : ℂ)) * (lambda : ℂ) = 1 := one_div_mul_cancel h_lam_c
    rw [h_cancel]
    simp

/-! ### 2. Real-coordinate readout for the single-mode zero -/

/-- 🏆 THEOREM 3: The reciprocal of a real eigenvalue is real -/
theorem fredholm_spectral_zero_is_real (lambda : ℝ) :
    ((1 / (lambda : ℂ)).im = 0) := by
  have h_ofReal : (1 / (lambda : ℂ)) = ((1 / lambda : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_ofReal]
  exact ofReal_im (1 / lambda)

/-! ### 3. Affine real-part readout (not a critical-line implication) -/

/-- 🏆 THEOREM 4: Affine real-part readout for s = w + 1/2 -/
theorem real_centered_zero_corresponds_to_critical_line (w : ℂ) :
    (w + 1 / 2 : ℂ).re = 1 / 2 + w.re := by
  simp [add_re]
  ring

/-/ The actual centered-coordinate critical-line criterion. -/
theorem centered_coordinate_on_critical_line_iff (w : ℂ) :
    (w + 1 / 2 : ℂ).re = 1 / 2 ↔ w.re = 0 := by
  rw [real_centered_zero_corresponds_to_critical_line]
  constructor <;> intro h <;> linarith

/-! ### 4. Master Fredholm Regularized Determinant Packet -/

/-- 🏆 THEOREM 5: MASTER FREDHOLM REGULARIZED DETERMINANT PACKET -/
theorem fredholm_regularized_determinant_master_packet
    (w : ℂ) (lambda : ℝ) (hlam : lambda ≠ 0) :
    -- 1. Regularized factor zero equivalence
    (fredholmFactor2 w lambda = 0 ↔ w = (1 / (lambda : ℂ))) ∧
    -- 2. Real spectral eigenvalue implies purely real zero locus
    ((1 / (lambda : ℂ)).im = 0) ∧
    -- 3. Non-vanishing of the exponential regulator
    (Complex.exp (w * (lambda : ℂ)) ≠ 0) :=
  ⟨fredholmFactor2_zero_iff w lambda hlam,
   fredholm_spectral_zero_is_real lambda,
   fredholm_regulator_nonvanishing w lambda⟩

end InfoGeometry.Topology.FredholmRegularizedDeterminantBridge
