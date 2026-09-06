import Mathlib.Data.Complex.BigOperators
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportOperatorKernel

/-!
# Positivity of the finite-support GNS vector state

This continues the finite Lean reimplementation of AFP
`Gelfand_Naimark_Segal`.  The AFP construction starts from a positive
functional; here we prove the corresponding positivity statement for the
finite-support vector state.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportStatePositivity

open scoped BigOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- Each positive-square summand is the squared complex norm. -/
theorem positive_square_term_eq_norm_sq (a : Alg n) (i : Active p) :
    involution a i.1 * a i.1 = (‖a i.1‖ ^ 2 : ℂ) := by
  simp [involution, Complex.conj_mul']

/-- The finite state of `a†a` is the complexification of the GNS squared norm. -/
theorem omega_positive_square_eq_normInner (a : Alg n) :
    omega p (fun i => involution a i * a i) =
      (normInnerGNS p (restrict p a) : ℂ) := by
  unfold omega normInnerGNS restrict
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa using positive_square_term_eq_norm_sq p a i

/-- The finite GNS squared norm is nonnegative. -/
theorem normInnerGNS_nonneg (a : Alg n) :
    0 ≤ normInnerGNS p (restrict p a) := by
  unfold normInnerGNS
  exact Finset.sum_nonneg fun i _ => sq_nonneg ‖restrict p a i‖

/-- Positivity of the real part of the state on positive squares. -/
theorem omega_positive_square_re_nonneg (a : Alg n) :
    0 ≤ (omega p (fun i => involution a i * a i)).re := by
  rw [omega_positive_square_eq_normInner]
  simp [normInnerGNS_nonneg p a]

/-- The state of a positive square is real. -/
theorem omega_positive_square_im_zero (a : Alg n) :
    (omega p (fun i => involution a i * a i)).im = 0 := by
  rw [omega_positive_square_eq_normInner]
  exact Complex.ofReal_im _

/-- Packaged positivity of the finite-support vector state. -/
theorem omega_positive_square_positive (a : Alg n) :
    0 ≤ (omega p (fun i => involution a i * a i)).re ∧
      (omega p (fun i => involution a i * a i)).im = 0 := by
  exact ⟨omega_positive_square_re_nonneg p a, omega_positive_square_im_zero p a⟩

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportStatePositivity
