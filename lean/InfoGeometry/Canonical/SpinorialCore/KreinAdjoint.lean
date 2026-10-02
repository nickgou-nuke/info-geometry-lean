import Mathlib

/-!
# Fundamental symmetries and the Krein adjoint

The indefinite adjoint is not silently substituted for the positive Hilbert
adjoint. A rational matrix witness separates their respective isometries.
-/

namespace InfoGeometry.Canonical.SpinorialCore.Krein

variable {A : Type*} [Ring A] [StarRing A]

def sharp (J X : A) : A := J * star X * J

theorem sharp_add (J X Y : A) : sharp J (X + Y) = sharp J X + sharp J Y := by
  simp [sharp, mul_add, add_mul]

theorem sharp_neg (J X : A) : sharp J (-X) = -sharp J X := by
  simp [sharp]

theorem sharp_sub (J X Y : A) : sharp J (X - Y) = sharp J X - sharp J Y := by
  simp [sharp, mul_sub, sub_mul]

theorem sharp_one (J : A) (hJ : J * J = 1) : sharp J 1 = 1 := by
  simpa [sharp] using hJ

theorem sharp_mul (J X Y : A) (hJ : J * J = 1) :
    sharp J (X * Y) = sharp J Y * sharp J X := by
  simp only [sharp, star_mul]
  calc
    J * (star Y * star X) * J = J * star Y * (J * J) * star X * J := by
      rw [hJ]; simp [mul_assoc]
    _ = (J * star Y * J) * (J * star X * J) := by noncomm_ring

theorem sharp_involutive (J : A) (hs : star J = J) (hJ : J * J = 1) :
    Function.Involutive (sharp J) := by
  intro X
  simp only [sharp, star_mul, star_star, hs]
  calc
    J * (J * (X * J)) * J = (J * J) * X * (J * J) := by noncomm_ring
    _ = X := by rw [hJ]; simp

def IsIsometry (J U : A) : Prop := star U * J * U = J

theorem isIsometry_iff_sharp_mul (J U : A) (hJ : J * J = 1) :
    IsIsometry J U ↔ sharp J U * U = 1 := by
  constructor
  · intro h
    change J * star U * J * U = 1
    calc
      J * star U * J * U = J * (star U * J * U) := by noncomm_ring
      _ = 1 := by rw [h, hJ]
  · intro h
    have hh := congrArg (fun x : A => J * x) h
    change J * (J * star U * J * U) = J * 1 at hh
    have hr : J * (J * star U * J * U) = (J * J) * (star U * J * U) := by
      noncomm_ring
    rw [hr, hJ, one_mul, mul_one] at hh
    exact hh

theorem isIsometry_mul (J U V : A) (hU : IsIsometry J U) (hV : IsIsometry J V) :
    IsIsometry J (U * V) := by
  change star (U * V) * J * (U * V) = J
  rw [star_mul]
  calc
    star V * star U * J * (U * V) = star V * (star U * J * U) * V := by
      noncomm_ring
    _ = J := by rw [hU]; exact hV

/-- Skew operators remain skew under the ordinary commutator bracket. -/
theorem sharp_commutator (J X Y : A) (hJ : J * J = 1)
    (hX : sharp J X = -X) (hY : sharp J Y = -Y) :
    sharp J (X * Y - Y * X) = -(X * Y - Y * X) := by
  rw [sharp_sub, sharp_mul J X Y hJ, sharp_mul J Y X hJ, hX, hY]
  noncomm_ring

/-- The algebraic adjoint calculation for a Clifford boost product. -/
theorem clifford_boost_skew (J W : A) (hs : star J = J)
    (hJ : J * J = 1) (hW : star W = -W) :
    sharp J (J * W) = -(J * W) := by
  simp only [sharp, star_mul, hs, hW]
  calc
    J * (-W * J) * J = -(J * W) * (J * J) := by noncomm_ring
    _ = -(J * W) := by rw [hJ, mul_one]

namespace Counterexample
open Matrix

def signature : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]
def boost : Matrix (Fin 2) (Fin 2) ℚ := !![5 / 4, 3 / 4; 3 / 4, 5 / 4]

theorem boost_preserves_signature : boost.transpose * signature * boost = signature := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boost, signature, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem boost_not_orthogonal : boost.transpose * boost ≠ 1 := by
  intro h
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [boost, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h0

end Counterexample
end InfoGeometry.Canonical.SpinorialCore.Krein
