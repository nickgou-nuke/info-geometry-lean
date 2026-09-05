import InfoGeometry.Algebra.SpinCore
import Mathlib.Tactic

/-!
# Nilpotent generators and invertible unipotent shifts

The N factor of an Iwasawa-type matrix decomposition is a unipotent GROUP
factor, not a nilpotent matrix. This local construction reuses the existing
square-zero rational raising matrix to exhibit the distinction explicitly.
-/

namespace InfoGeometry.Streaming.UnipotentMemoryShift

open InfoGeometry.Algebra.SpinCore

section Algebra
variable {A : Type*} [Ring A]

/-- A square-zero generator produces an actual unit, with a finite inverse formula. -/
def unipotentUnit (n : A) (hn : n * n = 0) : Aˣ where
  val := 1 + n
  inv := 1 - n
  val_inv := by
    calc
      (1 + n) * (1 - n) = 1 - n * n := by noncomm_ring
      _ = 1 := by rw [hn, sub_zero]
  inv_val := by
    calc
      (1 - n) * (1 + n) = 1 - n * n := by noncomm_ring
      _ = 1 := by rw [hn, sub_zero]

/-- No positive power of an invertible shift vanishes in a nontrivial algebra. -/
theorem unipotentUnit_pow_ne_zero [Nontrivial A] (n : A) (hn : n * n = 0) (k : ℕ) :
    ((unipotentUnit n hn : A) ^ k) ≠ 0 := by
  simpa using ((unipotentUnit n hn) ^ k).ne_zero
end Algebra

/-- The existing rational spin raising matrix is used as a memory-shift generator. -/
def shiftGenerator (t : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := t • J_plus

theorem shiftGenerator_sq (t : ℚ) : shiftGenerator t * shiftGenerator t = 0 := by
  simp [shiftGenerator, smul_mul_assoc, mul_smul_comm, j_plus_nilpotent]

/-- Concrete upper-unitriangular shift on the native two-coordinate carrier. -/
def memoryShift (t : ℚ) : (Matrix (Fin 2) (Fin 2) ℚ)ˣ :=
  unipotentUnit (shiftGenerator t) (shiftGenerator_sq t)

theorem memoryShift_add (s t : ℚ) : memoryShift (s + t) = memoryShift s * memoryShift t := by
  apply Units.ext
  change 1 + (s + t) • J_plus = (1 + s • J_plus) * (1 + t • J_plus)
  simp [add_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, j_plus_nilpotent] <;> abel

/-- Even though the generator squares to zero, the group element has no zero power. -/
theorem memoryShift_pow_ne_zero (t : ℚ) (k : ℕ) :
    ((memoryShift t : Matrix (Fin 2) (Fin 2) ℚ) ^ k) ≠ 0 :=
  unipotentUnit_pow_ne_zero _ _ _

end InfoGeometry.Streaming.UnipotentMemoryShift
