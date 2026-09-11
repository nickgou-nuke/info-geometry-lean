import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generic q-CCR residual owner

This owner contains the noncommutative residual
`c * cstar - q * cstar * c - 1` for an arbitrary ring.  Its boundary
lemmas identify the Cuntz, CAR, and CCR relations without introducing a
representation or a commutative model.
-/

namespace InfoGeometry.OperatorAlgebra.QCCRResidual

variable {R : Type*} [Ring R]

def qCcrRelation (c cstar : R) (q : R) : R :=
  c * cstar - q * cstar * c - 1

theorem cuntz_isometry_zero_law (S Sstar : R) (h : Sstar * S = 1) :
    Sstar * S - 1 = 0 := by
  rw [h]
  simp

theorem qccr_to_cuntz_limit (c cstar : R) :
    qCcrRelation c cstar 0 = 0 ↔ c * cstar = 1 := by
  dsimp [qCcrRelation]
  rw [zero_mul, zero_mul, sub_zero, sub_eq_zero]

/-- q-CCR equations are preserved by Ring homomorphisms. -/
theorem qCcrRelation_map (f : R →+* R) (c cstar q : R) :
    f (qCcrRelation c cstar q) =
      qCcrRelation (f c) (f cstar) (f q) := by
  dsimp [qCcrRelation]
  simp

/-- Forward transport: a vanishing q-CCR relation remains vanishing after map. -/
theorem qCcrRelation_map_zero (f : R →+* R) {c cstar q : R}
    (h : qCcrRelation c cstar q = 0) :
    qCcrRelation (f c) (f cstar) (f q) = 0 := by
  simpa [qCcrRelation_map] using congrArg f h

theorem qccr_bosonic_limit (a astar : R) :
    qCcrRelation a astar 1 = 0 ↔ a * astar - astar * a = 1 := by
  dsimp [qCcrRelation]
  rw [one_mul, sub_eq_zero]

theorem qccr_fermionic_limit (a astar : R) :
    qCcrRelation a astar (-1) = 0 ↔ a * astar + astar * a = 1 := by
  dsimp [qCcrRelation]
  rw [neg_one_mul, neg_mul, sub_neg_eq_add, sub_eq_zero]

theorem qccr_quadratic_reconstruction (a astar q : R) :
    qCcrRelation a astar q = 0 ↔ a * astar = 1 + q * astar * a := by
  dsimp [qCcrRelation]
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm]

theorem car_is_neg_one_qccr (a astar : R) (h : a * astar + astar * a = 1) :
    qCcrRelation a astar (-1) = 0 := by
  rw [qCcrRelation, neg_one_mul, neg_mul, sub_neg_eq_add, h, sub_self]

theorem ccr_is_plus_one_qccr (b bstar : R) (h : b * bstar - bstar * b = 1) :
    qCcrRelation b bstar 1 = 0 := by
  rw [qCcrRelation, one_mul, h, sub_self]

theorem qccr_vacuum_expectation (E : R → ℝ) (c cstar : R) (q : R) (q_val : ℝ)
    (h_qccr : E (qCcrRelation c cstar q) = 0)
    (h_vac : E (cstar * c) = 0)
    (h_lin : ∀ x y, E (x - y) = E x - E y)
    (h_one : E 1 = 1)
    (h_smul : E (q * cstar * c) = q_val * E (cstar * c)) :
    E (c * cstar) = 1 := by
  dsimp [qCcrRelation] at h_qccr
  rw [h_lin, h_lin, h_smul, h_vac, mul_zero, sub_zero, h_one] at h_qccr
  linarith

end InfoGeometry.OperatorAlgebra.QCCRResidual
