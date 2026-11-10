import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# TriFacetGeometry

Finite ring projector algebra for a tripotent element `T`
satisfying `T ^ 3 = T` over any (possibly non-commutative) ring `[Ring F] [Invertible (2 : F)]`.

The module proves that the hyperbolic, elliptic, and parabolic projectors
partition unity, are idempotent under the tripotent law, and are pairwise
orthogonal.  It is a finite algebraic surface, not a global spectral theorem.
-/

namespace InfoGeometry.Canonical.TriFacetGeometry

variable {F : Type*} [Ring F] [Invertible (2 : F)]

/-- In any ring `[Ring F]` with `Invertible (2 : F)`, `⅟(2 : F)` commutes with every element. -/
theorem invOf_two_comm (X : F) : ⅟(2 : F) * X = X * ⅟(2 : F) := by
  calc
    ⅟(2 : F) * X = ⅟(2 : F) * (X * ((2 : F) * ⅟(2 : F))) := by rw [mul_invOf_self, mul_one]
    _ = (⅟(2 : F) * (X * (2 : F))) * ⅟(2 : F) := by noncomm_ring
    _ = (⅟(2 : F) * ((2 : F) * X)) * ⅟(2 : F) := by
      have h2 : X * (2 : F) = (2 : F) * X := by noncomm_ring
      rw [h2]
    _ = ((⅟(2 : F) * (2 : F)) * X) * ⅟(2 : F) := by noncomm_ring
    _ = X * ⅟(2 : F) := by rw [invOf_mul_self, one_mul]

/-- The Hyperbolic projection operator P_hyp = (T² + T)/2. -/
def P_hyp (T : F) : F := ⅟(2 : F) * (T^2 + T)

/-- The Elliptic projection operator P_ell = (T² - T)/2. -/
def P_ell (T : F) : F := ⅟(2 : F) * (T^2 - T)

/-- The Parabolic (Harmonic Kernel) projection operator P_par = 1 - T². -/
def P_par (T : F) : F := 1 - T^2

/-- The three projection operators partition unity. -/
theorem P_sum (T : F) : P_hyp T + P_ell T + P_par T = 1 := by
  unfold P_hyp P_ell P_par
  calc
    ⅟(2 : F) * (T^2 + T) + ⅟(2 : F) * (T^2 - T) + (1 - T^2)
        = ((⅟(2 : F) * (2 : F)) * T^2) + (1 - T^2) := by noncomm_ring
    _ = T^2 + (1 - T^2) := by rw [invOf_mul_self (2 : F), one_mul]
    _ = 1 := by noncomm_ring

omit [Invertible (2 : F)] in
/-- T³ = T implies T⁴ = T². -/
theorem T_pow4 (T : F) (hT : T^3 = T) : T^4 = T^2 := by
  calc
    T^4 = T * T^3 := by noncomm_ring
    _ = T * T := by rw [hT]
    _ = T^2 := by noncomm_ring

/-- The Hyperbolic projector is idempotent under T³ = T. -/
theorem P_hyp_idem (T : F) (hT : T^3 = T) : P_hyp T * P_hyp T = P_hyp T := by
  unfold P_hyp
  have hT4 : T^4 = T^2 := T_pow4 T hT
  have h_sq : (T^2 + T) * (T^2 + T) = (2 : F) * (T^2 + T) := by
    calc
      (T^2 + T) * (T^2 + T) = T^4 + (2 : F) * T^3 + T^2 := by noncomm_ring
      _ = T^2 + (2 : F) * T + T^2 := by rw [hT4, hT]
      _ = (2 : F) * (T^2 + T) := by noncomm_ring
  calc
    (⅟(2 : F) * (T^2 + T)) * (⅟(2 : F) * (T^2 + T))
        = ⅟(2 : F) * ((T^2 + T) * ⅟(2 : F)) * (T^2 + T) := by noncomm_ring
    _ = ⅟(2 : F) * (⅟(2 : F) * (T^2 + T)) * (T^2 + T) := by rw [← invOf_two_comm (T^2 + T)]
    _ = (⅟(2 : F) * ⅟(2 : F)) * ((T^2 + T) * (T^2 + T)) := by noncomm_ring
    _ = (⅟(2 : F) * ⅟(2 : F)) * ((2 : F) * (T^2 + T)) := by rw [h_sq]
    _ = (⅟(2 : F) * (⅟(2 : F) * (2 : F))) * (T^2 + T) := by noncomm_ring
    _ = (⅟(2 : F) * 1) * (T^2 + T) := by rw [invOf_mul_self (2 : F)]
    _ = ⅟(2 : F) * (T^2 + T) := by noncomm_ring

/-- The Elliptic projector is idempotent under T³ = T. -/
theorem P_ell_idem (T : F) (hT : T^3 = T) : P_ell T * P_ell T = P_ell T := by
  unfold P_ell
  have hT4 : T^4 = T^2 := T_pow4 T hT
  have h_sq : (T^2 - T) * (T^2 - T) = (2 : F) * (T^2 - T) := by
    calc
      (T^2 - T) * (T^2 - T) = T^4 - (2 : F) * T^3 + T^2 := by noncomm_ring
      _ = T^2 - (2 : F) * T + T^2 := by rw [hT4, hT]
      _ = (2 : F) * (T^2 - T) := by noncomm_ring
  calc
    (⅟(2 : F) * (T^2 - T)) * (⅟(2 : F) * (T^2 - T))
        = ⅟(2 : F) * ((T^2 - T) * ⅟(2 : F)) * (T^2 - T) := by noncomm_ring
    _ = ⅟(2 : F) * (⅟(2 : F) * (T^2 - T)) * (T^2 - T) := by rw [← invOf_two_comm (T^2 - T)]
    _ = (⅟(2 : F) * ⅟(2 : F)) * ((T^2 - T) * (T^2 - T)) := by noncomm_ring
    _ = (⅟(2 : F) * ⅟(2 : F)) * ((2 : F) * (T^2 - T)) := by rw [h_sq]
    _ = (⅟(2 : F) * (⅟(2 : F) * (2 : F))) * (T^2 - T) := by noncomm_ring
    _ = (⅟(2 : F) * 1) * (T^2 - T) := by rw [invOf_mul_self (2 : F)]
    _ = ⅟(2 : F) * (T^2 - T) := by noncomm_ring

omit [Invertible (2 : F)] in
/-- The Parabolic projector is idempotent under T³ = T. -/
theorem P_par_idem (T : F) (hT : T^3 = T) : P_par T * P_par T = P_par T := by
  unfold P_par
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (1 - T^2) * (1 - T^2) = 1 - (2 : F) * T^2 + T^4 := by noncomm_ring
    _ = 1 - (2 : F) * T^2 + T^2 := by rw [hT4]
    _ = 1 - T^2 := by noncomm_ring

/-- Hyperbolic and Elliptic projectors are orthogonal under T³ = T. -/
theorem P_hyp_ell_orth (T : F) (hT : T^3 = T) : P_hyp T * P_ell T = 0 := by
  unfold P_hyp P_ell
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (⅟(2 : F) * (T^2 + T)) * (⅟(2 : F) * (T^2 - T))
        = ⅟(2 : F) * ((T^2 + T) * ⅟(2 : F)) * (T^2 - T) := by noncomm_ring
    _ = ⅟(2 : F) * (⅟(2 : F) * (T^2 + T)) * (T^2 - T) := by rw [← invOf_two_comm (T^2 + T)]
    _ = (⅟(2 : F) * ⅟(2 : F)) * (T^4 - T^2) := by noncomm_ring
    _ = (⅟(2 : F) * ⅟(2 : F)) * (T^2 - T^2) := by rw [hT4]
    _ = 0 := by noncomm_ring

/-- Hyperbolic and Parabolic projectors are orthogonal under T³ = T. -/
theorem P_hyp_par_orth (T : F) (hT : T^3 = T) : P_hyp T * P_par T = 0 := by
  unfold P_hyp P_par
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (⅟(2 : F) * (T^2 + T)) * (1 - T^2) = ⅟(2 : F) * (T^2 + T - T^4 - T^3) := by noncomm_ring
    _ = ⅟(2 : F) * (T^2 + T - T^2 - T) := by rw [hT4, hT]
    _ = 0 := by noncomm_ring

/-- Elliptic and Parabolic projectors are orthogonal under T³ = T. -/
theorem P_ell_par_orth (T : F) (hT : T^3 = T) : P_ell T * P_par T = 0 := by
  unfold P_ell P_par
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (⅟(2 : F) * (T^2 - T)) * (1 - T^2) = ⅟(2 : F) * (T^2 - T - T^4 + T^3) := by noncomm_ring
    _ = ⅟(2 : F) * (T^2 - T - T^2 + T) := by rw [hT4, hT]
    _ = 0 := by noncomm_ring

/-- Parabolic and Hyperbolic projectors are orthogonal on the left under T³ = T. -/
theorem P_par_hyp_orth (T : F) (hT : T^3 = T) : P_par T * P_hyp T = 0 := by
  unfold P_par P_hyp
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (1 - T^2) * (⅟(2 : F) * (T^2 + T))
        = ((1 - T^2) * ⅟(2 : F)) * (T^2 + T) := by noncomm_ring
    _ = (⅟(2 : F) * (1 - T^2)) * (T^2 + T) := by rw [← invOf_two_comm (1 - T^2)]
    _ = ⅟(2 : F) * (T^2 + T - T^4 - T^3) := by noncomm_ring
    _ = ⅟(2 : F) * (T^2 + T - T^2 - T) := by rw [hT4, hT]
    _ = 0 := by noncomm_ring

/-- Parabolic and Elliptic projectors are orthogonal on the left under T³ = T. -/
theorem P_par_ell_orth (T : F) (hT : T^3 = T) : P_par T * P_ell T = 0 := by
  unfold P_par P_ell
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (1 - T^2) * (⅟(2 : F) * (T^2 - T))
        = ((1 - T^2) * ⅟(2 : F)) * (T^2 - T) := by noncomm_ring
    _ = (⅟(2 : F) * (1 - T^2)) * (T^2 - T) := by rw [← invOf_two_comm (1 - T^2)]
    _ = ⅟(2 : F) * (T^2 - T - T^4 + T^3) := by noncomm_ring
    _ = ⅟(2 : F) * (T^2 - T - T^2 + T) := by rw [hT4, hT]
    _ = 0 := by noncomm_ring

end InfoGeometry.Canonical.TriFacetGeometry
