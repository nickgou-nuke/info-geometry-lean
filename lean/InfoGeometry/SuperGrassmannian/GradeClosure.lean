/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

namespace InfoGeometry.SuperGrassmannian.GradeClosure

open scoped Matrix
open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
open InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

variable {R : Type*} [CommRing R]

/-- The Cartan adjoint action assigns grade +1 to the first odd contact generator. -/
theorem adH_E01_grade_one :
    adH (E 0 1 : Matrix (Fin 3) (Fin 3) R) = E 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [adH_00, E]
  · exact adH_01 _
  · simp [adH_02, E]
  · simp [adH_10, E]
  · simp [adH_11, E]
  · simp [adH_12, E]
  · simp [adH_20, E]
  · simp [adH_21, E]
  · simp [adH_22, E]

/-- The Cartan adjoint action assigns grade +1 to the second odd contact generator. -/
theorem adH_E12_grade_one :
    adH (E 1 2 : Matrix (Fin 3) (Fin 3) R) = E 1 2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [adH_00, E]
  · simp [adH_01, E]
  · simp [adH_02, E]
  · simp [adH_10, E]
  · simp [adH_11, E]
  · exact adH_12 _
  · simp [adH_20, E]
  · simp [adH_21, E]
  · simp [adH_22, E]

/-- The odd contact bracket is grade additive: the bracket of the two grade-one
    generators is the grade-two generator, and the Cartan action has weight 2. -/
theorem adH_odd_contact_grade_add :
    adH (bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2)) =
      2 • bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2) := by
  rw [odd_contact_bracket]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [adH_00, E]
  · simp [adH_01, E]
  · simpa [E] using (adH_02 (R := R) (E 0 2 : Matrix (Fin 3) (Fin 3) R))
  · simp [adH_10, E]
  · simp [adH_11, E]
  · simp [adH_12, E]
  · simp [adH_20, E]
  · simp [adH_21, E]
  · simp [adH_22, E]

/-- The preceding grade-additivity identity is the concrete specialization of
    the commutator derivation law. -/
theorem adH_odd_contact_derivation :
    adH (bracket (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2)) =
      bracket (adH (E 0 1 : Matrix (Fin 3) (Fin 3) R)) (E 1 2) +
      bracket (E 0 1) (adH (E 1 2)) := by
  simpa [adH, H_grading, H, bracket] using
    (derivation_identity (R := R) (H R)
      (E 0 1 : Matrix (Fin 3) (Fin 3) R) (E 1 2))

end InfoGeometry.SuperGrassmannian.GradeClosure
