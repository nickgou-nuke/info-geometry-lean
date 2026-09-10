import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.SplitCliffordChiralProjection
import InfoGeometry.Canonical.ModularSL2R

/-!
# InfoGeometry.Canonical.DrazinAnomalousProjector

Finite projector/orthogonality identities on the `M₂(ℝ)` seed.

This file proves:
1. `N_left + N_right = 1` (completeness),
2. trace-orthogonality of `N_left, N_right` against the nilpotent boundary `N`,
3. `traceForm K N = 0` via chiral decomposition.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.DrazinAnomalousProjector

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.SplitCliffordChiralProjection
open InfoGeometry.Canonical.ModularSL2R

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Completeness of chiral Moore-Penrose projectors. -/
theorem mp_projector_completeness :
    N_left + N_right = (1 : M2R) := by
  rw [N_left_eval, N_right_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/-- Left projector is trace-orthogonal to the nilpotent boundary `N`. -/
theorem trace_N_left_boundary :
    traceForm N_left N = 0 := by
  unfold traceForm tr
  rw [N_left_eval]
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right projector is trace-orthogonal to the nilpotent boundary `N`. -/
theorem trace_N_right_boundary :
    traceForm N_right N = 0 := by
  unfold traceForm tr
  rw [N_right_eval]
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Modular generator orthogonality to boundary from chiral decomposition.
-/
theorem trace_K_boundary_from_MP :
    traceForm InfoGeometry.Canonical.ModularLorentzBoost.K N = 0 := by
  have hKN :
      traceForm InfoGeometry.Canonical.ModularLorentzBoost.K N = 0 ∧
      traceForm InfoGeometry.Canonical.ModularLorentzBoost.K Nᵀ = 0 := traceForm_K_N
  exact hKN.1

/-- Left chiral projector preserves boundary `N` on the left. -/
theorem N_left_mul_boundary :
    N_left * N = N := by
  rw [N_left_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right chiral projector preserves boundary `N` on the right. -/
theorem boundary_mul_N_right :
    N * N_right = N := by
  rw [N_right_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left projector kills `N` on the right. -/
theorem boundary_mul_N_left_zero :
    N * N_left = 0 := by
  rw [N_left_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right projector kills `N` on the left. -/
theorem N_right_mul_boundary_zero :
    N_right * N = 0 := by
  rw [N_right_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral projectors are orthogonal under multiplication. -/
theorem chiral_projectors_mul_zero :
    N_left * N_right = 0 ∧ N_right * N_left = 0 := by
  constructor
  · rw [N_left_eval, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [N_left_eval, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/--
Trace pairing with `K` splits as the difference of chiral pairings.
-/
theorem trace_K_boundary_split :
    traceForm InfoGeometry.Canonical.ModularLorentzBoost.K N =
      traceForm N_left N - traceForm N_right N := by
  rw [K_eq_chiral_difference]
  unfold traceForm tr
  norm_num [N, N_left_eval, N_right_eval, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.DrazinAnomalousProjector
