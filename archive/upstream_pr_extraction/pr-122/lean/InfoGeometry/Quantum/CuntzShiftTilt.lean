import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.CuntzShiftTilt

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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
    (S * X * star S) * (S * Y * star S)
      = (S * X * star S) * (S * (Y * star S)) := by rw [mul_assoc S Y (star S)]
    _ = (S * X) * (star S * (S * (Y * star S))) := by rw [mul_assoc (S * X) (star S) (S * (Y * star S))]
    _ = (S * X) * ((star S * S) * (Y * star S)) := by rw [← mul_assoc (star S) S (Y * star S)]
    _ = (S * X) * (1 * (Y * star S)) := by rw [hS]
    _ = (S * X) * (Y * star S) := by rw [one_mul]
    _ = ((S * X) * Y) * star S := by rw [mul_assoc (S * X) Y (star S)]
    _ = (S * (X * Y)) * star S := by rw [mul_assoc S X Y]

theorem tilt_is_isometry (S q : R) (hS : IsCuntzIsometry S) (hq_unit : IsUnitaryPhase q) :
    IsCuntzIsometry (CuntzTilt S q) := by
  unfold IsCuntzIsometry CuntzTilt IsUnitaryPhase at *
  rw [star_mul]
  calc
    (star S * star q) * (q * S)
      = star S * (star q * (q * S)) := by rw [mul_assoc (star S) (star q) (q * S)]
    _ = star S * ((star q * q) * S) := by rw [← mul_assoc (star q) q S]
    _ = star S * (1 * S) := by rw [hq_unit.1]
    _ = star S * S := by rw [one_mul]
    _ = 1 := by rw [hS]

theorem shift_tilt_invariant (S X q : R) (hq_unit : IsUnitaryPhase q)
    (hq_cent_star : IsCentral (star q)) :
    CuntzShift (CuntzTilt S q) X = CuntzShift S X := by
  unfold CuntzShift CuntzTilt IsUnitaryPhase IsCentral at *
  rw [star_mul]
  have step1 : (q * S) * X * (star S * star q) = q * (S * X * star S) * star q := by
    calc
      (q * S) * X * (star S * star q)
        = ((q * S) * X * star S) * star q := by rw [mul_assoc ((q * S) * X) (star S) (star q)]
      _ = (q * (S * X) * star S) * star q := by rw [mul_assoc q S X]
      _ = (q * (S * X * star S)) * star q := by rw [mul_assoc q (S * X) (star S)]
  rw [step1]
  have step2 : q * (S * X * star S) * star q = q * (star q * (S * X * star S)) := by
    have hc := hq_cent_star (S * X * star S)
    calc
      q * (S * X * star S) * star q
        = q * ((S * X * star S) * star q) := by rw [mul_assoc]
      _ = q * (star q * (S * X * star S)) := by rw [hc]
  rw [step2]
  have step3 : q * (star q * (S * X * star S)) = (q * star q) * (S * X * star S) := by
    rw [← mul_assoc]
  rw [step3]
  have h_unit : q * star q = 1 := hq_unit.2
  rw [h_unit, one_mul]

theorem grand_cuntz_shift_tilt_synthesis (S X Y q : R) (hS : IsCuntzIsometry S)
    (hq_unit : IsUnitaryPhase q) (hq_cent_star : IsCentral (star q)) :
    (CuntzShift S X * CuntzShift S Y = CuntzShift S (X * Y)) ∧
    (IsCuntzIsometry (CuntzTilt S q)) ∧
    (CuntzShift (CuntzTilt S q) X = CuntzShift S X) :=
  ⟨shift_multiplicative S X Y hS,
   tilt_is_isometry S q hS hq_unit,
   shift_tilt_invariant S X q hq_unit hq_cent_star⟩

end InfoGeometry.Quantum.CuntzShiftTilt
