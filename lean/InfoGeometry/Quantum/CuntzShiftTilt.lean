import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

namespace InfoGeometry.Quantum.CuntzShiftTilt

variable {R : Type*} [Ring R] [StarRing R]

def IsCuntzIsometry (S : R) : Prop := star S * S = 1
def IsUnitaryPhase (q : R) : Prop := star q * q = 1 ∧ q * star q = 1
def IsCentral (q : R) : Prop := ∀ x : R, q * x = x * q
def CuntzShift (S X : R) : R := S * X * star S
def CuntzTilt (S q : R) : R := q * S

theorem shift_multiplicative (S X Y : R) (hS : IsCuntzIsometry S) :
    CuntzShift S X * CuntzShift S Y = CuntzShift S (X * Y) := by
  unfold CuntzShift IsCuntzIsometry at *
  calc
    (S * X * star S) * (S * Y * star S) = (S * X) * (star S * S) * (Y * star S) := by simp only [mul_assoc]
    _ = (S * X) * (Y * star S) := by simp [hS]
    _ = S * (X * Y) * star S := by simp only [mul_assoc]

theorem tilt_is_isometry (S q : R) (hS : IsCuntzIsometry S)
    (hq_unit : IsUnitaryPhase q) : IsCuntzIsometry (CuntzTilt S q) := by
  unfold IsCuntzIsometry CuntzTilt IsUnitaryPhase at *
  rw [star_mul]
  calc
    (star S * star q) * (q * S) = star S * (star q * q) * S := by simp only [mul_assoc]
    _ = star S * S := by simp [hq_unit.1]
    _ = 1 := hS

theorem shift_tilt_invariant (S X q : R) (hq_unit : IsUnitaryPhase q)
    (hq_cent_star : IsCentral (star q)) :
    CuntzShift (CuntzTilt S q) X = CuntzShift S X := by
  unfold CuntzShift CuntzTilt IsUnitaryPhase IsCentral at *
  rw [star_mul]
  calc
    (q * S) * X * (star S * star q) = q * (S * X * star S) * star q := by simp only [mul_assoc]
    _ = q * (star q * (S * X * star S)) := by rw [hq_cent_star]; simp only [mul_assoc]
    _ = (q * star q) * (S * X * star S) := by rw [← mul_assoc]
    _ = S * X * star S := by rw [hq_unit.2, one_mul]

theorem grand_cuntz_shift_tilt_synthesis (S X Y q : R) (hS : IsCuntzIsometry S)
    (hq_unit : IsUnitaryPhase q) (hq_cent_star : IsCentral (star q)) :
    (CuntzShift S X * CuntzShift S Y = CuntzShift S (X * Y)) ∧
    (IsCuntzIsometry (CuntzTilt S q)) ∧
    (CuntzShift (CuntzTilt S q) X = CuntzShift S X) :=
  ⟨shift_multiplicative S X Y hS, tilt_is_isometry S q hS hq_unit,
    shift_tilt_invariant S X q hq_unit hq_cent_star⟩

end InfoGeometry.Quantum.CuntzShiftTilt
