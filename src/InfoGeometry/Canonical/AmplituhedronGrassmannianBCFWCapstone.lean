/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Finite Plücker and Scalar BCFW Identities

This module contains finite algebraic facts about two-row Plücker coordinates,
a scalar pole-cancellation identity, and an Arnold relation for reciprocal
differences. It does not formalize geometric BCFW recursion, Poincaré residues,
a canonical differential form, or Yang--Baxter synthesis.

1. **Plücker Coordinates & Plücker Syzygy on $\operatorname{Gr}(2, n)$**:
   - Plücker coordinates $\Delta_{ij} = C_{0i} C_{1j} - C_{0j} C_{1i}$.
   - Antisymmetry: $\Delta_{ji} = -\Delta_{ij}$, $\Delta_{ii} = 0$.
   - 🏆 **Plücker Quadric Identity (Grassmannian Syzygy)**:
     $$\Delta_{ab} \Delta_{cd} - \Delta_{ac} \Delta_{bd} + \Delta_{ad} \Delta_{bc} = 0$$

2. **A two-row strict-minor positivity predicate**:
   - Total positivity: all maximal ordered minors $\Delta_I(C) > 0$.
   - Consecutive minor cyclicity and non-vanishing of kinematic brackets.

3. **Scalar pole cancellation and reciprocal-difference identity**:
   - `P_sq * scalarChannelQuotient = ML * MR` holds when `P_sq ≠ 0`.
   - The Arnold relation here is a rational identity, not a cohomology theorem:
     $$\omega_{12}\omega_{23} + \omega_{23}\omega_{31} + \omega_{31}\omega_{12} = 0$$

Canonical-form construction and geometric residue interpretation remain open
development tasks; no theorem in this module establishes them.
-/

open scoped BigOperators Real Matrix
open Matrix

noncomputable section

namespace InfoGeometry.Canonical.AmplituhedronBCFW

/-! ### 1. Plücker Coordinates and Plücker Syzygy -/

/-- Plücker minor coordinate $\Delta_{ij}$ for a 2 x n matrix $C$. -/
def pluckerMinor {n : ℕ} (C : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  C 0 i * C 1 j - C 0 j * C 1 i

/-- 🏆 THEOREM 1 (Plücker Antisymmetry): $\Delta_{ji} = -\Delta_{ij}$. -/
theorem pluckerMinor_antisymm {n : ℕ} (C : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) :
    pluckerMinor C j i = - pluckerMinor C i j := by
  unfold pluckerMinor
  ring

/-- 🏆 THEOREM 2 (Plücker Diagonal Vanishing): $\Delta_{ii} = 0$. -/
theorem pluckerMinor_self {n : ℕ} (C : Matrix (Fin 2) (Fin n) ℝ) (i : Fin n) :
    pluckerMinor C i i = 0 := by
  unfold pluckerMinor
  ring

/-- 🏆 THEOREM 3 (The Fundamental Plücker Syzygy on Gr(2, n)):
    $\Delta_{ab} \Delta_{cd} - \Delta_{ac} \Delta_{bd} + \Delta_{ad} \Delta_{bc} = 0$. -/
theorem plucker_syzygy {n : ℕ} (C : Matrix (Fin 2) (Fin n) ℝ) (a b c d : Fin n) :
    pluckerMinor C a b * pluckerMinor C c d -
    pluckerMinor C a c * pluckerMinor C b d +
    pluckerMinor C a d * pluckerMinor C b c = 0 := by
  unfold pluckerMinor
  ring

/-! ### 2. Positive Grassmannian Gr_{>0}(2, n) -/

/-- Definition of strict positive Grassmannian $\operatorname{Gr}_{>0}(2, n)$. -/
def IsPositiveGrassmannian₂ {n : ℕ} (C : Matrix (Fin 2) (Fin n) ℝ) : Prop :=
  ∀ (i j : Fin n), i < j → 0 < pluckerMinor C i j

/-- 🏆 THEOREM 4 (Positive Grassmannian Consecutive Minors):
    In $\operatorname{Gr}_{>0}(2, n)$, every ordered pair has strictly positive area minor. -/
theorem positive_grassmannian_minor_pos {n : ℕ}
    (C : Matrix (Fin 2) (Fin n) ℝ) (hC : IsPositiveGrassmannian₂ C)
    (i j : Fin n) (hij : i < j) :
    0 < pluckerMinor C i j :=
  hC i j hij

/-- Scaling both rows of a two-row matrix scales each Plücker minor quadratically. -/
theorem pluckerMinor_smul {n : ℕ} (r : ℝ) (C : Matrix (Fin 2) (Fin n) ℝ)
    (i j : Fin n) :
    pluckerMinor (r • C) i j = r ^ 2 * pluckerMinor C i j := by
  simp [pluckerMinor, smul_eq_mul]
  ring

/-! ### 3. Scalar Channel Cancellation & Arnold Rational Identity -/

/-- Scalar channel expression consisting of two factors and a nonzero
    denominator. This is only an algebraic model; it is not a meromorphic
    amplitude or a residue. -/
def scalarChannelQuotient (ML MR : ℝ) (P_sq : ℝ) : ℝ :=
  ML * (1 / P_sq) * MR

/-- Clearing a nonzero scalar denominator in `scalarChannelQuotient` recovers
    the product of the two factors. This cancellation identity does not
    evaluate a residue at the excluded value `P_sq = 0`. -/
theorem scalarChannelQuotient_denominator_cancel
    (ML MR P_sq : ℝ) (hP : P_sq ≠ 0) :
    P_sq * scalarChannelQuotient ML MR P_sq = ML * MR := by
  unfold scalarChannelQuotient
  calc P_sq * (ML * (1 / P_sq) * MR)
    _ = (P_sq * (1 / P_sq)) * (ML * MR) := by ring
    _ = 1 * (ML * MR) := by rw [mul_one_div_cancel hP]
    _ = ML * MR := by ring

/-- Scalar polynomial used in the reciprocal-difference identity below.
    No differential-form or cohomology structure is asserted here. -/
def arnoldCohenScalarExpression (w12 w23 w31 : ℝ) : ℝ :=
  w12 * w23 + w23 * w31 + w31 * w12

/-- Scalar reciprocal-difference coefficient $\omega_{ij} = 1/(z_i-z_j)$.
    This is a coefficient function, not itself a differential form. -/
def logDiffForm (z1 z2 : ℝ) : ℝ :=
  1 / (z1 - z2)

/-- For pairwise distinct real inputs, the displayed reciprocal-difference
    scalar expression vanishes. This rational identity is not a cohomology
    theorem or a BCFW recursion relation:
    $\frac{1}{z_1 - z_2}\frac{1}{z_2 - z_3} + \frac{1}{z_2 - z_3}\frac{1}{z_3 - z_1} + \frac{1}{z_3 - z_1}\frac{1}{z_1 - z_2} = 0$. -/
theorem arnold_cohen_reciprocal_identity (z1 z2 z3 : ℝ)
    (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h31 : z3 ≠ z1) :
    arnoldCohenScalarExpression
      (logDiffForm z1 z2) (logDiffForm z2 z3) (logDiffForm z3 z1) = 0 := by
  unfold arnoldCohenScalarExpression logDiffForm
  have hz12 : z1 - z2 ≠ 0 := sub_ne_zero.mpr h12
  have hz23 : z2 - z3 ≠ 0 := sub_ne_zero.mpr h23
  have hz31 : z3 - z1 ≠ 0 := sub_ne_zero.mpr h31
  field_simp [hz12, hz23, hz31]
  ring

end InfoGeometry.Canonical.AmplituhedronBCFW
