import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportStatePositivity

/-!
# Linearity and star compatibility of the finite-support GNS state

This continues the finite Lean reimplementation of AFP
`Gelfand_Naimark_Segal` / `Cstar_Algebra_On`.  The finite-support vector state
is a complex-linear functional and is compatible with the C*-involution.
-/

noncomputable section

namespace GNSFiniteSupportStateLinear

open scoped BigOperators
open GNSFiniteSupport

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- The finite-support state preserves addition. -/
theorem omega_add (a b : Alg n) :
    omega p (a + b) = omega p a + omega p b := by
  unfold omega
  simp [Finset.sum_add_distrib]

/-- The finite-support state preserves negation. -/
theorem omega_neg (a : Alg n) :
    omega p (-a) = - omega p a := by
  unfold omega
  simp [Finset.sum_neg_distrib]

/-- The finite-support state preserves subtraction. -/
theorem omega_sub (a b : Alg n) :
    omega p (a - b) = omega p a - omega p b := by
  unfold omega
  simp [Finset.sum_sub_distrib]

/-- The finite-support state preserves complex scalar multiplication. -/
theorem omega_smul (c : ℂ) (a : Alg n) :
    omega p (c • a) = c * omega p a := by
  unfold omega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The finite-support state intertwines involution with complex conjugation. -/
theorem omega_involution (a : Alg n) :
    omega p (involution a) = star (omega p a) := by
  unfold omega involution
  rw [star_sum]

/-- If `a` is self-adjoint, then `omega a` is real. -/
theorem omega_self_adjoint_im_zero (a : Alg n) (ha : involution a = a) :
    (omega p a).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have hstar : star (omega p a) = omega p a := by
    rw [← omega_involution]
    rw [ha]
  simpa [Complex.star_def] using hstar

end GNSFiniteSupportStateLinear
