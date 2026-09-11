/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The canonical `Cl(1,1)` quadratic algebra is represented concretely by the
split-quaternion matrix model from `Cl11SplitQuaternionMobiusBridge`.
-/
import InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

namespace InfoGeometry.Canonical.Cl11MatrixCliffordBridge

open InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge
open BottPeriodicityReconciliation
open InfoGeometry.Clifford
open Matrix

abbrev Cl11 := CliffordAlgebra splitQ11

/-- Linear map sending the two split Clifford coordinates to the matrix
generators `splitL` and `splitI`. -/
noncomputable def matrixGenerator : (ℝ × ℝ) →ₗ[ℝ] SplitQuaternion where
  toFun v := v.1 • splitL + v.2 • splitI
  map_add' := by
    intro u v
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a v
    simp [smul_add, smul_smul]

/-- The matrix generators satisfy the defining quadratic relation of `splitQ11`.
This is the metric-closure obligation required by the Clifford universal
property. -/
lemma matrixGenerator_sq (v : ℝ × ℝ) :
    matrixGenerator v * matrixGenerator v =
      algebraMap ℝ SplitQuaternion (splitQ11 v) := by
  rcases v with ⟨a, b⟩
  change (a • splitL + b • splitI) * (a • splitL + b • splitI) =
    algebraMap ℝ SplitQuaternion (splitQ11 (a, b))
  calc
    (a • splitL + b • splitI) * (a • splitL + b • splitI) =
        (a * a - b * b) • splitOne := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
      have hIL : splitL * splitI + splitI * splitL = 0 := by
        simpa [add_comm] using splitI_splitL_anticommute
      rw [splitL_sq, splitI_sq]
      have hLI : splitL * splitI = -(splitI * splitL) :=
        eq_neg_of_add_eq_zero_left hIL
      rw [hLI]
      module
    _ = algebraMap ℝ SplitQuaternion (splitQ11 (a, b)) := by
      simp [splitOne, I2, splitQ11_apply, Algebra.algebraMap_eq_smul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, Matrix.one_apply]

/-- The universal-property lift from the abstract Clifford algebra to the
concrete split-quaternion matrix algebra. -/
noncomputable def cl11MatrixRep : Cl11 →ₐ[ℝ] SplitQuaternion :=
  CliffordAlgebra.lift splitQ11 ⟨matrixGenerator, matrixGenerator_sq⟩

@[simp] theorem cl11MatrixRep_ι (v : ℝ × ℝ) :
    cl11MatrixRep (CliffordAlgebra.ι splitQ11 v) = matrixGenerator v := by
  simp [cl11MatrixRep]

theorem cl11MatrixRep_jGen :
    cl11MatrixRep (CliffordAlgebra.ι splitQ11 (1, 0)) = splitL := by
  rw [cl11MatrixRep_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixGenerator]

theorem cl11MatrixRep_kGen :
    cl11MatrixRep (CliffordAlgebra.ι splitQ11 (0, 1)) = splitI := by
  rw [cl11MatrixRep_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixGenerator]

theorem cl11MatrixRep_nullGenerator :
    cl11MatrixRep (CliffordAlgebra.ι splitQ11 (1, 1)) = splitNull := by
  rw [cl11MatrixRep_ι]
  change (1 : ℝ) • splitL + (1 : ℝ) • splitI = splitNull
  simp [splitNull]

/-- The Clifford lift is onto the full noncommutative split-quaternion matrix
algebra.  The proof uses the existing four-element matrix basis span and the
universal-property images of the two Clifford generators. -/
theorem cl11MatrixRep_surjective : Function.Surjective cl11MatrixRep := by
  intro A
  obtain ⟨a, b, c, d, hA⟩ := splitQuaternion_basis_span A
  let x : Cl11 :=
    a • (1 : Cl11) +
      b • CliffordAlgebra.ι splitQ11 (1, 0) +
      c • CliffordAlgebra.ι splitQ11 (0, 1) +
      d • (CliffordAlgebra.ι splitQ11 (0, 1) *
        CliffordAlgebra.ι splitQ11 (1, 0))
  refine ⟨x, ?_⟩
  rw [hA]
  simp only [x, map_add, map_smul, map_one, map_mul,
    cl11MatrixRep_jGen, cl11MatrixRep_kGen]
  have hOne : (1 : SplitQuaternion) = splitOne := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitOne, I2, Matrix.one_apply]
  simpa [hOne, splitIL]

end InfoGeometry.Canonical.Cl11MatrixCliffordBridge
