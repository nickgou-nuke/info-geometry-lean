/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
import InfoGeometry.Topology.WittenJonesTemperleyLiebTransport

/-!
# Candidate: comparison of ordinary and parity-aware brackets

This file connects the ordinary matrix commutator used by the finite
Kantor--Tanaka owner to the shared parity-aware bracket.  The comparison is
made only where the matrix multiplication itself proves the required
orthogonality; no identification of the two bracket notions is asserted for
arbitrary odd pairs.
-/

namespace InfoGeometry.SuperGrassmannian.GradedBracketComparison

open scoped Matrix BigOperators

namespace SB

open InfoGeometry.Algebra.SupergradedBracket

variable {A : Type*} [Ring A]

/-- If the reverse product vanishes, the ordinary commutator agrees with the
odd--odd superbracket. -/
theorem commutator_eq_superBracket_odd_odd_of_reverse_mul_eq_zero
    {x y : A} (h : y * x = 0) :
    commutator x y = superBracket true true x y := by
  rw [superBracket_odd_odd]
  change x * y - y * x = x * y + y * x
  rw [h]
  simp

end SB

namespace Contact

open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

/- The concrete matrix comparison is intentionally specialized to `ℂ`, whose
   existing native matrix witness is imported above. -/

private theorem reverse_contact_product_zero :
    (E 1 2 : Matrix (Fin 3) (Fin 3) ℂ) * E 0 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply]

/-- The ordinary Kantor contact bracket agrees with the parity-aware
odd--odd bracket because the reverse matrix product vanishes. -/
theorem kantor_contact_bracket_eq_superBracket :
    bracket (E 0 1 : Matrix (Fin 3) (Fin 3) ℂ) (E 1 2) =
      superBracket true true (E 0 1) (E 1 2) := by
  change commutator (E 0 1 : Matrix (Fin 3) (Fin 3) ℂ) (E 1 2) =
    superBracket true true (E 0 1) (E 1 2)
  exact SB.commutator_eq_superBracket_odd_odd_of_reverse_mul_eq_zero
    reverse_contact_product_zero

private theorem reverse_conjugate_contact_product_zero :
    (E 1 0 : Matrix (Fin 3) (Fin 3) ℂ) * E 2 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply]

/-- The conjugate ordinary contact bracket also agrees with the
parity-aware odd--odd bracket under the corresponding vanishing product. -/
theorem kantor_conjugate_contact_bracket_eq_superBracket :
    bracket (E 2 1 : Matrix (Fin 3) (Fin 3) ℂ) (E 1 0) =
      superBracket true true (E 2 1) (E 1 0) := by
  change commutator (E 2 1 : Matrix (Fin 3) (Fin 3) ℂ) (E 1 0) =
    superBracket true true (E 2 1) (E 1 0)
  exact SB.commutator_eq_superBracket_odd_odd_of_reverse_mul_eq_zero
    reverse_conjugate_contact_product_zero

end Contact

end InfoGeometry.SuperGrassmannian.GradedBracketComparison
