/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.MaxRelativeEntropy
import InfoGeometry.Quantum.DensityMatrixPurity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A noncommuting qubit support obstruction

The existing Bloch density matrices at `(0, 0, 1)` and `(1, 0, 0)` are
normalized positive states that do not commute. The effect at `(-1, 0, 0)`
has Born weight `1 / 2` on the first state and zero on the reference state.
The native operator-domination divergence is therefore infinite.

All operators remain full `Fin 2` complex matrices. Positivity is proved
using native rank-one matrices, and the infinite value follows from the
general positive trace-witness theorem.
-/

noncomputable section
namespace InfoGeometry.Quantum.MaxRelativeEntropyQubit

open Matrix
open DensityMatrixPurity
open InfoGeometry.OperatorAlgebra.MaxRelativeEntropy
open scoped ComplexOrder MatrixOrder

/-- The positive z-axis Bloch matrix is a normalized positive state. -/
theorem z_state :
    (densityMatrix 0 0 1).PosSemidef ∧ trace (densityMatrix 0 0 1) = 1 := by
  refine ⟨?_, densityMatrix_trace 0 0 1⟩
  have h : densityMatrix 0 0 1 =
      vecMulVec (![1, 0] : Fin 2 → ℂ) (star (![1, 0] : Fin 2 → ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [densityMatrix, vecMulVec, Pi.star_apply]
  rw [h]
  exact posSemidef_vecMulVec_self_star _

/-- The positive x-axis Bloch matrix is a normalized positive state. -/
theorem x_state :
    (densityMatrix 1 0 0).PosSemidef ∧ trace (densityMatrix 1 0 0) = 1 := by
  refine ⟨?_, densityMatrix_trace 1 0 0⟩
  have h : densityMatrix 1 0 0 = (1 / 2 : ℝ) •
      vecMulVec (![1, 1] : Fin 2 → ℂ) (star (![1, 1] : Fin 2 → ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [densityMatrix, vecMulVec, Pi.star_apply, Matrix.smul_apply,
        Complex.real_smul]
  rw [h]
  exact (posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The negative x-axis Bloch matrix is also a normalized positive state. -/
theorem neg_x_state :
    (densityMatrix (-1) 0 0).PosSemidef ∧
      trace (densityMatrix (-1) 0 0) = 1 := by
  refine ⟨?_, densityMatrix_trace (-1) 0 0⟩
  have h : densityMatrix (-1) 0 0 = (1 / 2 : ℝ) •
      vecMulVec (![1, -1] : Fin 2 → ℂ) (star (![1, -1] : Fin 2 → ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [densityMatrix, vecMulVec, Pi.star_apply, Matrix.smul_apply,
        Complex.real_smul]
  rw [h]
  exact (posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- These two normalized states genuinely fail to commute. -/
theorem z_x_mul_ne_mul :
    densityMatrix 0 0 1 * densityMatrix 1 0 0 ≠
      densityMatrix 1 0 0 * densityMatrix 0 0 1 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [densityMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The negative x-axis state is a measurement effect; its complement is
the positive x-axis state. -/
theorem neg_x_is_effect :
    0 ≤ densityMatrix (-1) 0 0 ∧ densityMatrix (-1) 0 0 ≤ 1 := by
  refine ⟨neg_x_state.1.nonneg, ?_⟩
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) - densityMatrix (-1) 0 0 =
      densityMatrix 1 0 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [densityMatrix]
  rw [Matrix.le_iff, h]
  exact x_state.1

/-- The support-detecting effect has strictly positive input Born weight. -/
theorem born_z_neg_x :
    trace (densityMatrix 0 0 1 * densityMatrix (-1) 0 0) = (1 / 2 : ℂ) := by
  norm_num [densityMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- The same effect has zero reference Born weight. -/
theorem born_x_neg_x :
    trace (densityMatrix 1 0 0 * densityMatrix (-1) 0 0) = 0 := by
  norm_num [densityMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- The actual extended max-relative entropy of these noncommuting
normalized states is infinite, witnessed by a genuine measurement effect. -/
theorem maxRelativeEntropy_z_x :
    maxRelativeEntropy (densityMatrix 0 0 1) (densityMatrix 1 0 0) = ⊤ := by
  apply InfoGeometry.Quantum.MaxRelativeEntropy.maxRelativeEntropy_eq_top_of_trace_witness
    (E := densityMatrix (-1) 0 0) neg_x_state.1 born_x_neg_x
  rw [born_z_neg_x]
  norm_num [Complex.lt_def]

end InfoGeometry.Quantum.MaxRelativeEntropyQubit
