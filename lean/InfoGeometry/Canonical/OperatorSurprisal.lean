import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularLorentzBoost
import InfoGeometry.Canonical.SplitCliffordChiralProjection
import InfoGeometry.Canonical.EmergentKillingField

/-!
# InfoGeometry.Canonical.OperatorSurprisal

Operator surprisal as a scaled modular generator and its chiral trace readout.
-/

namespace InfoGeometry.Canonical.OperatorSurprisal

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularLorentzBoost
open InfoGeometry.Canonical.SplitCliffordChiralProjection
open InfoGeometry.Canonical.EmergentKillingField

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Operator surprisal: `β • K`. -/
noncomputable def surprisal (β : ℝ) : M2R := β • K

/-- Surprisal commutator on the nilpotent boundary is the `2β` boost scaling. -/
theorem surprisal_generates_hyperbolic_boost (β : ℝ) :
    surprisal β * N - N * surprisal β = (2 * β) • N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [surprisal, K, N, E, I, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Chiral left trace readout of surprisal is `β`. -/
theorem surprisal_trace_left (β : ℝ) :
    traceForm (surprisal β) N_left = β := by
  unfold traceForm tr surprisal
  rw [K_eval, N_left_eval]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral right trace readout of surprisal is `-β`. -/
theorem surprisal_trace_right (β : ℝ) :
    traceForm (surprisal β) N_right = -β := by
  unfold traceForm tr surprisal
  rw [K_eval, N_right_eval]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Total surprisal readout on `N_left + N_right` is balanced to `0`. -/
theorem surprisal_total_equilibrium (β : ℝ) :
    traceForm (surprisal β) (N_left + N_right) = 0 := by
  rw [N_left_eval, N_right_eval]
  unfold traceForm tr surprisal
  rw [K_eval]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.OperatorSurprisal
