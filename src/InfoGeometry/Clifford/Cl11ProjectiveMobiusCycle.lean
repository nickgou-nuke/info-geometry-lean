/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

/-!
# Projective Möbius cycle readouts in the finite `2 × 2` real matrix model

This module proves homogeneous Cayley identities in the concrete matrix
carrier and relates the Cayley generator to the Peirce-sheet commutator. It
uses matrix generators and Peirce-projector results from
`Cl11ProjectiveMobiusBridge`. It does not construct a topology on a
projective quotient, a limiting point at infinity, or an arithmetic
Dirichlet-series identity.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11ProjectiveMobiusCycle

open InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge
open Matrix

/-- Homogeneous Cayley coordinate in the real two-dimensional Clifford
matrix model. The denominator condition is kept explicit in theorems that use
this chart formula. -/
def homogeneousCayley (u v : ℝ) : M2R :=
  ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2)) • (1 : M2R) +
    ((2 * u * v) / (u ^ 2 + v ^ 2)) • e1

/-- The polynomial numerator of the Cayley chart is the square
`(u I + v e1)^2`. Multiplying the opposite-sign factors instead gives the
scalar norm `(u^2 + v^2) I`, so these two factorizations must not be
conflated. -/
theorem cayleyNumerator_eq_square (u v : ℝ) :
    (u • (1 : M2R) + v • e1) ^ 2 =
      (u ^ 2 - v ^ 2) • (1 : M2R) + (2 * u * v) • e1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The opposite-sign factors have scalar product `(u^2 + v^2) I`; this is
the denominator-clearing norm identity for the normalized Cayley chart. -/
theorem cayleyOppositeFactors (u v : ℝ) :
    (u • (1 : M2R) + v • e1) * (u • (1 : M2R) - v • e1) =
      (u ^ 2 + v ^ 2) • (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- In this concrete matrix carrier, the skew generator in the Cayley chart is
the commutator of the first Peirce sheet with the sheet-swap involution. -/
theorem sheetSwap_commutator_eq_e1 :
    Pminus * e0 - e0 * Pminus = e1 := by
  rw [Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1]

/-- The normalized Cayley chart can be expressed using the intrinsic
Peirce-sheet commutator, linking the projective chart stage to the Cayley
stage without asserting a topological circle or a projective quotient. -/
theorem homogeneousCayley_eq_peirce_commutator (u v : ℝ) :
    homogeneousCayley u v =
      ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2)) • (1 : M2R) +
        ((2 * u * v) / (u ^ 2 + v ^ 2)) • (Pminus * e0 - e0 * Pminus) := by
  rw [homogeneousCayley, ← sheetSwap_commutator_eq_e1]

/-- Reversing the sign of the second homogeneous coordinate gives a right
inverse for the homogeneous Cayley matrix. -/
theorem homogeneousCayley_mul_reflection (u v : ℝ)
    (h : u ^ 2 + v ^ 2 ≠ 0) :
    homogeneousCayley u v * homogeneousCayley u (-v) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homogeneousCayley, e1, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [h] <;> ring

/-- Swapping homogeneous coordinates reverses the Cayley orientation and
negates the reflected chart value. This is a formula identity; it does not
identify projective representatives in a quotient. -/
theorem homogeneousCayley_swap (u v : ℝ) :
    homogeneousCayley v u = -homogeneousCayley u (-v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homogeneousCayley, e1] <;> ring

/-- Exact homogeneous Cayley values at the coordinate anchors `(1,0)`, `(1,1)`,
and `(0,1)`. The middle pair is only an algebraic input; no projective
midpoint structure is defined here. -/
theorem homogeneousCayley_anchors :
    homogeneousCayley 1 0 = 1 ∧
    homogeneousCayley 1 1 = e1 ∧
    homogeneousCayley 0 1 = -1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [homogeneousCayley, e1]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [homogeneousCayley, e1] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [homogeneousCayley, e1]

end InfoGeometry.Clifford.Cl11ProjectiveMobiusCycle
