/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exact idempotency-defect transfer through a Schur complement

The coefficient ring is arbitrary and may itself be a full matrix ring or an
endomorphism ring. The two-sided inverse equations concern its unit `1`.
They are not ambient inverse equations for an element of a proper Peirce
corner, whose corner unit is an idempotent rather than the ambient unit.

For `M = !![a, b; c, d]` and `a * u = u * a = 1`, the tail is
`S = d - c * u * b`. Its defect is obtained from the four blocks of `M²-M`
by an exact ordered formula. The final equivalence characterizes idempotence
by the head equation, the two coupling annihilation equations, and
idempotence of the tail. No commutation, positivity, nonvanishing correction,
or automatic existence of a subsequent pivot is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.SchurIdempotencyDefect

open InfoGeometry.Core.IdempotencyDefect
open Matrix

variable {R B : Type*} [Ring R] [Ring B]

/-- All four ordered defect blocks, in the native matrix ring. -/
theorem defect_block (a b c d : R) :
    defect (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) =
      !![a * a + b * c - a, a * b + b * d - b;
         c * a + d * c - c, c * b + d * d - d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [defect]

/-- Idempotence is equivalent to vanishing of the four displayed defects. -/
theorem block_isIdempotentElem_iff (a b c d : R) :
    IsIdempotentElem (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) ↔
      a * a + b * c - a = 0 ∧
      a * b + b * d - b = 0 ∧
      c * a + d * c - c = 0 ∧
      c * b + d * d - d = 0 := by
  rw [← defect_eq_zero_iff, defect_block]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
    · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h
    · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) h
    · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) h
  · rintro ⟨haa, hab, hca, hdd⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [haa, hab, hca, hdd]

/-- The upper coupling defect is the tail coupling plus the head defect
transported on the right. A right inverse of the head is sufficient here. -/
theorem upper_defect_eq (a b c d u : R) (hau : a * u = 1) :
    a * b + b * d - b =
      b * (d - c * u * b) + (a * a + b * c - a) * u * b := by
  have hau' (x : R) : a * (u * x) = x := by
    rw [← mul_assoc, hau, one_mul]
  noncomm_ring [hau, hau']

/-- The lower coupling defect is the tail coupling plus the head defect
transported on the left. A left inverse of the head is sufficient here. -/
theorem lower_defect_eq (a b c d u : R) (hua : u * a = 1) :
    c * a + d * c - c =
      (d - c * u * b) * c + c * u * (a * a + b * c - a) := by
  have hua' (x : R) : u * (a * x) = x := by
    rw [← mul_assoc, hua, one_mul]
  noncomm_ring [hua, hua']

/-- Exact defect descent only needs the two inverse equations after acting
on the upper coupling. This formulation also applies to a proper Peirce
corner, without equating its unit with the ambient ring unit. -/
theorem schur_defect_of_coupling_inverse (a b c d u : R)
    (hau : a * (u * b) = b) (hua : u * (a * b) = b) :
    defect (d - c * u * b) =
      (c * b + d * d - d) -
      (c * a + d * c - c) * u * b -
      c * u * (a * b + b * d - b) +
      c * u * (a * a + b * c - a) * u * b := by
  unfold defect
  noncomm_ring [hau, hua]

/-- A two-sided inverse of the head supplies the two coupling equations.
Every mixed product retains its original order. -/
theorem schur_defect (a b c d u : R)
    (hau : a * u = 1) (hua : u * a = 1) :
    defect (d - c * u * b) =
      (c * b + d * d - d) -
      (c * a + d * c - c) * u * b -
      c * u * (a * b + b * d - b) +
      c * u * (a * a + b * c - a) * u * b := by
  apply schur_defect_of_coupling_inverse a b c d u
  · rw [← mul_assoc, hau, one_mul]
  · rw [← mul_assoc, hua, one_mul]

/-- The same transfer is the lower-right compression of the original defect
between the two elimination factors. These factors need not be mutual
inverses, so this statement does not assert conjugacy of the two defects. -/
theorem schur_defect_eq_compressed (a b c d u : R)
    (hau : a * u = 1) (hua : u * a = 1) :
    defect (d - c * u * b) =
      ((!![1, 0; -(c * u), 1] : Matrix (Fin 2) (Fin 2) R) *
        defect (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) *
        !![1, -(u * b); 0, 1]) 1 1 := by
  rw [schur_defect a b c d u hau hua, defect_block]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  noncomm_ring

/-- An exact structural characterization: the head defect, both ordered
couplings to the tail, and the tail defect are the complete obstruction. -/
theorem block_isIdempotentElem_iff_schur (a b c d u : R)
    (hau : a * u = 1) (hua : u * a = 1) :
    IsIdempotentElem (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) ↔
      a * a + b * c - a = 0 ∧
      b * (d - c * u * b) = 0 ∧
      (d - c * u * b) * c = 0 ∧
      defect (d - c * u * b) = 0 := by
  constructor
  · intro hM
    obtain ⟨haa, hab, hca, hdd⟩ := (block_isIdempotentElem_iff a b c d).1 hM
    refine ⟨haa, ?_, ?_, ?_⟩
    · have h := upper_defect_eq a b c d u hau
      rw [hab, haa] at h
      simpa only [zero_mul, add_zero] using h.symm
    · have h := lower_defect_eq a b c d u hua
      rw [hca, haa] at h
      simpa only [mul_zero, add_zero] using h.symm
    · rw [schur_defect a b c d u hau hua, haa, hab, hca, hdd]
      simp
  · rintro ⟨haa, hbs, hsc, hss⟩
    have hab : a * b + b * d - b = 0 := by
      rw [upper_defect_eq a b c d u hau, haa, hbs]
      simp
    have hca : c * a + d * c - c = 0 := by
      rw [lower_defect_eq a b c d u hua, haa, hsc]
      simp
    have hdd : c * b + d * d - d = 0 := by
      have h := schur_defect a b c d u hau hua
      rw [haa, hab, hca, hss] at h
      simpa only [zero_mul, mul_zero, sub_zero, add_zero] using h.symm
    exact (block_isIdempotentElem_iff a b c d).2 ⟨haa, hab, hca, hdd⟩

/-- A block idempotent with a two-sided invertible head has an idempotent
Schur tail in the coefficient ring. -/
theorem schur_isIdempotentElem_of_block (a b c d u : R)
    (hau : a * u = 1) (hua : u * a = 1)
    (hM : IsIdempotentElem (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R)) :
    IsIdempotentElem (d - c * u * b) := by
  apply (defect_eq_zero_iff _).1
  exact ((block_isIdempotentElem_iff_schur a b c d u hau hua).1 hM).2.2.2

/-- The descent theorem accepts an arbitrary native two-by-two matrix,
allowing the coefficient ring itself to be a lower stage in a matrix tower. -/
theorem schur_isIdempotentElem (M : Matrix (Fin 2) (Fin 2) R) (u : R)
    (hau : M 0 0 * u = 1) (hua : u * M 0 0 = 1)
    (hM : IsIdempotentElem M) :
    IsIdempotentElem (M 1 1 - M 1 0 * u * M 0 1) := by
  apply schur_isIdempotentElem_of_block (M 0 0) (M 0 1) (M 1 0) (M 1 1) u hau hua
  simpa only [← Matrix.eta_fin_two M] using hM

/-- Ring homomorphisms preserve the ordered Schur expression. Together with
the existing `map_defect` theorem this transports the exact defect identity. -/
theorem map_schur (f : R →+* B) (b c d u : R) :
    f (d - c * u * b) = f d - f c * f u * f b := by
  simp only [map_sub, map_mul]

end InfoGeometry.OperatorAlgebra.SchurIdempotencyDefect
