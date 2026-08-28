import Mathlib

/-!
# Generic Clifford-style ideal readbacks

The statements below use only associativity and an explicit idempotent.  They
do not identify a Clifford algebra with a matrix algebra or assert a spinor
dimension.
-/
namespace InfoGeometry.Clifford

variable {Cl : Type*} [Ring Cl]

def LeftIdeal (P : Cl) := {x : Cl | x * P = x}
def RightIdeal (P : Cl) := {y : Cl | P * y = y}

theorem left_mul_mem (P : Cl) (g : Cl) (x : LeftIdeal P) :
    g * x.1 ∈ LeftIdeal P := by
  change (g * x.1) * P = g * x.1
  rw [mul_assoc, x.2]

theorem right_mul_mem (P : Cl) (y : RightIdeal P) (g : Cl) :
    y.1 * g ∈ RightIdeal P := by
  change P * (y.1 * g) = y.1 * g
  rw [← mul_assoc, y.2]

theorem corner_pairing (P : Cl) (x : LeftIdeal P) (y : RightIdeal P) :
    P * (y.1 * x.1) * P = y.1 * x.1 := by
  calc
    P * (y.1 * x.1) * P = (P * y.1) * (x.1 * P) := by
      simp only [mul_assoc]
    _ = y.1 * x.1 := by rw [y.2, x.2]

end InfoGeometry.Clifford
