/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Weyl.OperatorBraiding
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A noncentral operator-valued braiding witness

Two integer transvection units label the edges and vertices of a two-vertex
swap. The coefficient ring is `M₂(ℤ)` and the clock/shift carrier is
`M₂(M₂(ℤ))`. The resulting holonomy coefficient is neither scalar nor central.
-/

namespace InfoGeometry.Weyl.OperatorBraidingExamples

open Matrix OperatorBraiding

abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

def upperUnit : Coeffˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def lowerUnit : Coeffˣ where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def swapVertices : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def edgeLabels : Fin 2 → Coeffˣ := fun _ => upperUnit
def vertexLabels : Fin 2 → Coeffˣ := fun _ => lowerUnit

/-- The coefficient labels themselves do not commute. -/
theorem coefficient_units_noncommute : ¬ Commute upperUnit lowerUnit := by
  intro h
  have hh := congrArg (fun u : Coeffˣ => (u : Coeff) 0 0) h.eq
  norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- Explicit ordered plaquette readout at the first vertex. -/
theorem holonomy_value :
    ((braidingHolonomy swapVertices edgeLabels vertexLabels 0 : Coeffˣ) : Coeff) =
      !![0, 1; -1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [braidingHolonomy_apply, edgeLabels, vertexLabels,
      upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- The off-diagonal entry excludes every scalar multiple of the identity. -/
theorem holonomy_not_scalar (z : ℤ) :
    ((braidingHolonomy swapVertices edgeLabels vertexLabels 0 : Coeffˣ) : Coeff) ≠
      Matrix.scalar (Fin 2) z := by
  intro h
  have hh := congrArg (fun M : Coeff => M 0 1) h
  rw [holonomy_value] at hh
  change (1 : ℤ) = 0 at hh
  norm_num at hh

/-- The holonomy fails to commute with an explicit coefficient-ring element. -/
theorem holonomy_noncentral :
    ¬ Commute ((braidingHolonomy swapVertices edgeLabels vertexLabels 0 : Coeffˣ) : Coeff)
      (upperUnit : Coeff) := by
  intro h
  have hh := congrArg (fun M : Coeff => M 0 0) h.eq
  rw [holonomy_value] at hh
  norm_num [upperUnit, Matrix.mul_apply, Fin.sum_univ_two] at hh

theorem holonomy_ne_one :
    braidingHolonomy swapVertices edgeLabels vertexLabels 0 ≠ 1 := by
  intro h
  have hh := congrArg (fun u : Coeffˣ => (u : Coeff) 0 1) h
  rw [holonomy_value] at hh
  norm_num at hh

/-- Nonflat holonomy forces noncommutation in the unit group of the nested matrix ring. -/
theorem clock_shift_units_noncommute :
    ¬ Commute (clockUnit vertexLabels) (shiftUnit swapVertices edgeLabels) := by
  intro h
  exact holonomy_ne_one ((clockUnit_shiftUnit_commute_iff
    swapVertices edgeLabels vertexLabels).mp h 0)

/-- The same noncommutation in the native ring `M₂(M₂(ℤ))`. -/
theorem clock_shift_matrices_noncommute :
    ¬ Commute (clock vertexLabels) (shift swapVertices edgeLabels) := by
  intro h
  apply clock_shift_units_noncommute
  change clockUnit vertexLabels * shiftUnit swapVertices edgeLabels =
    shiftUnit swapVertices edgeLabels * clockUnit vertexLabels
  apply Units.ext
  exact h.eq

end InfoGeometry.Weyl.OperatorBraidingExamples
