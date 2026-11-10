import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.IdempotentCornerCommutant

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

theorem leftIdeal_mul_closed (P : Cl) (x y : LeftIdeal P) :
    x.1 * y.1 ∈ LeftIdeal P := by
  change (x.1 * y.1) * P = x.1 * y.1
  rw [mul_assoc, y.2]

theorem rightIdeal_mul_closed (P : Cl) (x y : RightIdeal P) :
    x.1 * y.1 ∈ RightIdeal P := by
  change P * (x.1 * y.1) = x.1 * y.1
  rw [← mul_assoc, x.2]

theorem leftIdeal_add_closed (P : Cl) (x y : LeftIdeal P) :
    x.1 + y.1 ∈ LeftIdeal P := by
  change (x.1 + y.1) * P = x.1 + y.1
  rw [add_mul, x.2, y.2]

theorem rightIdeal_add_closed (P : Cl) (x y : RightIdeal P) :
    x.1 + y.1 ∈ RightIdeal P := by
  change P * (x.1 + y.1) = x.1 + y.1
  rw [mul_add, x.2, y.2]

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

theorem corner_pairing_mem
    (P : Cl) (_hP : P * P = P)
    (x : LeftIdeal P) (y : RightIdeal P) :
    ∃ c : InfoGeometry.Algebra.IdempotentCornerCommutant.Corner P,
      c.1 = y.1 * x.1 := by
  refine ⟨⟨y.1 * x.1, ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, y.2]
  · rw [mul_assoc, x.2]

end InfoGeometry.Clifford
