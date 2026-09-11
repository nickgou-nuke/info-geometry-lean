import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

theorem neg_sq_twisted_fix_of_anticomm
    {A : Type*} [Ring A]
    (e f : A)
    (hff : f * f = -1)
    (hanti : f * e + e * f = 0) :
    -f * e * (-f) = e := by
  have hfe : f * e = -(e * f) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hanti
  calc
    -f * e * (-f) = f * e * f := by noncomm_ring
    _ = -(e * f) * f := by rw [hfe]
    _ = e := by
      calc
        -(e * f) * f = -((e * f) * f) := by rw [neg_mul]
        _ = -(e * (f * f)) := by rw [mul_assoc]
        _ = e := by rw [hff]; simp

end InfoGeometry.Clifford.Clifford55
