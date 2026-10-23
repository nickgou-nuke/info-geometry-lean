/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cuntz2Isometries
import InfoGeometry.Canonical.FiniteCantorBranchAmplification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite-dimensional obstruction for Cuntz O₂ generators

The normalized matrix trace tower is a genuine noncommutative UHF tower, but
it cannot itself be a stagewise `Cuntz2Isometries` tower: two isometries with
orthogonal ranges would force `2 * dim = dim`.  This theorem records that
trace obstruction explicitly, preventing an invalid concrete Cuntz
instantiation at finite matrix stages.

The constructive finite replacement is the existing rectangular branch system.
`FiniteCantorCuntzBranches.amplify` refines arbitrary endomorphisms between
successive word stages, preserves identity and composition, is injective,
and intertwines the diagonal bonding map on vectors.
-/

namespace InfoGeometry.Canonical.FiniteMatrixCuntzObstruction

open CuntzAlgebra

theorem no_cuntz2_matrix {n : ℕ} (hn : 0 < n)
    (C : Cuntz2Isometries (Matrix (Fin n) (Fin n) ℂ)) : False := by
  have h₁ : Matrix.trace (CuntzAlgebra.S1 C * star (CuntzAlgebra.S1 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry1 C, Matrix.trace_one]
    simp
  have h₂ : Matrix.trace (CuntzAlgebra.S2 C * star (CuntzAlgebra.S2 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry2 C, Matrix.trace_one]
    simp
  have hsum := congrArg Matrix.trace (CuntzAlgebra.h_range_sum C)
  rw [Matrix.trace_add, h₁, h₂, Matrix.trace_one] at hsum
  have hnat' : n + n = Fintype.card (Fin n) := by
    exact_mod_cast hsum
  have hnat : n + n = n := by
    simpa using hnat'
  omega

end InfoGeometry.Canonical.FiniteMatrixCuntzObstruction
