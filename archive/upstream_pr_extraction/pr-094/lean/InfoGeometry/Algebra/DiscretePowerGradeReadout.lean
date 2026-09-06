import Mathlib

/-!
# Discrete power/grade readout

The powers of an element form a monoid representation of the additive
natural-number grading.  This is the algebraic precursor of a Mellin readout;
no transform or analytic structure is asserted here.
-/

namespace InfoGeometry.Algebra.Spectra

variable {A : Type*} [Monoid A]

def discretePowerGradeReadout (X : A) : Multiplicative ℕ →* A where
  toFun n := X ^ (Multiplicative.toAdd n)
  map_one' := by
    change X ^ 0 = 1
    exact pow_zero X
  map_mul' m n := by
    change X ^ (Multiplicative.toAdd (m * n)) =
      X ^ (Multiplicative.toAdd m) * X ^ (Multiplicative.toAdd n)
    rw [show Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n by rfl]
    exact pow_add X _ _

@[simp] theorem discretePowerGradeReadout_apply
    (X : A) (k : ℕ) :
    discretePowerGradeReadout X (Multiplicative.ofAdd k) = X ^ k := rfl

theorem discretePowerGradeReadout_periodic
    {X : A} {n k : ℕ} (hn : 1 ≤ k) (hX : X ^ n = X) :
    X ^ (k + n - 1) = X ^ k := by
  have hkn : k + n - 1 = (k - 1) + n := by omega
  calc
    X ^ (k + n - 1) = X ^ ((k - 1) + n) := by rw [hkn]
    _ = X ^ (k - 1) * X ^ n := by rw [pow_add]
    _ = X ^ (k - 1) * X := by rw [hX]
    _ = X ^ ((k - 1) + 1) := by rw [pow_add, pow_one]
    _ = X ^ k := by congr 2; omega

def discretePowerGradeReadoutUnits (X : Aˣ) : Multiplicative ℤ →* Aˣ where
  toFun z := X ^ (Multiplicative.toAdd z)
  map_one' := by
    change X ^ (0 : ℤ) = 1
    exact zpow_zero X
  map_mul' m n := by
    change X ^ (Multiplicative.toAdd (m * n)) =
      X ^ (Multiplicative.toAdd m) * X ^ (Multiplicative.toAdd n)
    rw [show Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n by rfl]
    exact zpow_add X _ _

@[simp] theorem discretePowerGradeReadoutUnits_apply
    (X : Aˣ) (k : ℤ) :
    discretePowerGradeReadoutUnits X (Multiplicative.ofAdd k) = X ^ k := rfl

end InfoGeometry.Algebra.Spectra
