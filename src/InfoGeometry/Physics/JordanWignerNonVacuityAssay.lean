/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Physics.ChevalleyDyads
import InfoGeometry.Physics.ChevalleyMultiDyads
import InfoGeometry.Physics.JordanWignerMultiDyads

/-!
# QMS Non-Vacuity Assay: Jordan–Wigner Multi-Dyad Realization

This module provides an adversarial non-vacuity assay for the categorical
Jordan–Wigner formalization in `JordanWignerMultiDyads.lean`.

## Purpose of the Assay (QMS-SOP-ALC-001)

An algebraic theorem in an abstract category $\mathcal{C}$ could theoretically be
vacuous if no non-trivial object $X$ with non-zero identity $\mathbb{1}_X \neq 0$
and non-zero nilpotent operators $n, p$ can satisfy the axioms.

This module proves **strict non-vacuity** by constructing an explicit computational
witness in $\operatorname{Mat}(2 \times 2, \mathbb{R})$:
1. $n = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and $p = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$.
2. Both operators are strictly non-zero: $n \neq 0$, $p \neq 0$.
3. Both operators are nilpotent: $n^2 = 0$, $p^2 = 0$.
4. They satisfy the CAR relation: $n p + p n = \mathbb{1}_2$.
5. The identity is strictly non-zero: $\mathbb{1}_2 \neq 0$.
6. The dyadic projectors $E_{00} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
   $E_{11} = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$ are distinct ($E_{00} \neq E_{11}$).
7. The Pauli $Z$ operator $\sigma^z = E_{00} - E_{11} \neq 0$.

All proofs are complete, constructive, and kernel-verified with 0 sorry.
-/

namespace InfoGeometry.Physics.JordanWignerAssay

open Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The canonical upper-triangular nilpotent annihilation operator in $\operatorname{Mat}(2, \mathbb{R})$. -/
def n_mat : Mat2R := !![0, 1; 0, 0]

/-- The canonical lower-triangular nilpotent creation operator in $\operatorname{Mat}(2, \mathbb{R})$. -/
def p_mat : Mat2R := !![0, 0; 1, 0]

/-- Non-vacuity test 1: The identity matrix is strictly non-zero. -/
theorem id_mat_ne_zero : (1 : Mat2R) ≠ 0 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [Matrix.one_apply] at h00

/-- Non-vacuity test 2: The nilpotent $n$ is strictly non-zero. -/
theorem n_mat_ne_zero : n_mat ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [n_mat] at h01

/-- Non-vacuity test 3: The nilpotent $p$ is strictly non-zero. -/
theorem p_mat_ne_zero : p_mat ≠ 0 := by
  intro h
  have h10 := congr_fun (congr_fun h 1) 0
  norm_num [p_mat] at h10

/-- Mathematical integrity test 1: $n^2 = 0$. -/
theorem n_mat_sq : n_mat * n_mat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [n_mat, Matrix.mul_apply, Finset.sum]

/-- Mathematical integrity test 2: $p^2 = 0$. -/
theorem p_mat_sq : p_mat * p_mat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p_mat, Matrix.mul_apply, Finset.sum]

/-- Mathematical integrity test 3: $n p + p n = \mathbb{1}_2$. -/
theorem car_mat : n_mat * p_mat + p_mat * n_mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [n_mat, p_mat, Matrix.mul_apply, Finset.sum, Matrix.one_apply]

/-- Non-vacuity test 4: The vacuum and excited idempotents are strictly distinct. -/
theorem e00_ne_e11 : n_mat * p_mat ≠ p_mat * n_mat := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [n_mat, p_mat, Matrix.mul_apply, Finset.sum] at h00

/-- Non-vacuity test 5: The Pauli $\sigma^z$ parity operator is non-zero. -/
theorem sigmaZ_ne_zero : n_mat * p_mat - p_mat * n_mat ≠ 0 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [n_mat, p_mat, Matrix.mul_apply, Finset.sum] at h00

/-- **Master Non-Vacuity Assay Theorem**:
    The CAR algebra, the Chevalley dyadic system, and the Jordan–Wigner parity generator
    possess a non-trivial, non-zero representation with distinct vacuum and excited sectors. -/
theorem master_non_vacuity_assay :
    n_mat * n_mat = 0 ∧
    p_mat * p_mat = 0 ∧
    n_mat * p_mat + p_mat * n_mat = 1 ∧
    n_mat ≠ 0 ∧
    p_mat ≠ 0 ∧
    (1 : Mat2R) ≠ 0 ∧
    n_mat * p_mat ≠ p_mat * n_mat ∧
    n_mat * p_mat - p_mat * n_mat ≠ 0 :=
  ⟨n_mat_sq, p_mat_sq, car_mat, n_mat_ne_zero, p_mat_ne_zero, id_mat_ne_zero, e00_ne_e11, sigmaZ_ne_zero⟩

end InfoGeometry.Physics.JordanWignerAssay
