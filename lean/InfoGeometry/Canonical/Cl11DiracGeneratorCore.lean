/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.MatrixNoncommutativity

/-!
# The Cl(1,1) Dirac generator at a finite stage

Genuine proofs extracted from the placeholder-bearing `UHFCantorSpectralTriple`
stash lane.  The stash defined `diracGenerator` (Pauli X) but left its
self-adjointness and square laws as `by sorry`; both are proved here by direct
matrix computation with no proof hole.

The stash's higher-stage `uhfDirac` was itself a placeholder (returning the zero
matrix) whose claimed square/compatibility properties are false, so it is
deliberately not ported.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11DiracGeneratorCore

/-- Closed non-commutativity witness (T16). -/
theorem complexMat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix,
    InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix,
    InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne⟩

/-- The Cl(1,1) generator `γ₀ = J1 = [[0,1],[1,0]]` (Pauli X). -/
def diracGenerator : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Dirac generator is self-adjoint. -/
theorem diracGenerator_selfAdjoint :
    star diracGenerator = diracGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGenerator, Matrix.conjTranspose, Matrix.star_apply]

/-- The Dirac generator squares to the identity. -/
theorem diracGenerator_sq :
    diracGenerator * diracGenerator = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGenerator, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.Cl11DiracGeneratorCore
