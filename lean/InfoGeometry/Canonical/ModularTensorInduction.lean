import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordChiralProjection
import InfoGeometry.Canonical.ModularLorentzBoost
import InfoGeometry.Canonical.ModularSL2R
import InfoGeometry.Canonical.DrazinAnomalousProjector

/-!
# InfoGeometry.Canonical.ModularTensorInduction

Finite non-Taylor modular identities on the `M₂(ℝ)` seed.

This file proves exact projector-based formulas for the modular exponential
and boundary-trace invariants.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.ModularTensorInduction

open Matrix
open InfoGeometry.Canonical.SplitCliffordChiralProjection
open InfoGeometry.Canonical.ModularLorentzBoost
open InfoGeometry.Canonical.ModularSL2R
open InfoGeometry.Canonical.DrazinAnomalousProjector

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Exact projector formula for `exp(tK)`. -/
noncomputable def expKExact (t : ℝ) : M2R :=
  Real.exp t • N_left + Real.exp (-t) • N_right

/-- Base modular operator `Δ = exp(-K)` in the projector model. -/
noncomputable def DeltaBase : M2R := expKExact (-1)

/-- Base logarithm in the finite seed: `log Δ = -K`. -/
noncomputable def logDeltaBase : M2R := (-1 : ℝ) • K

/-- Explicit diagonal evaluation of `expKExact`. -/
theorem expKExact_eval (t : ℝ) :
    expKExact t = !![Real.exp t, 0; 0, Real.exp (-t)] := by
  unfold expKExact
  rw [N_left_eval, N_right_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/-- `exp(0K)=1`. -/
@[simp]
theorem expKExact_zero : expKExact 0 = (1 : M2R) := by
  rw [expKExact_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/-- Exact semigroup law for the finite modular exponential. -/
theorem expKExact_mul (s t : ℝ) :
    expKExact s * expKExact t = expKExact (s + t) := by
  rw [expKExact_eval, expKExact_eval, expKExact_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add] <;> ring_nf

/-- Exact inverse law in the finite projector model. -/
@[simp]
theorem expKExact_mul_neg (t : ℝ) :
    expKExact t * expKExact (-t) = (1 : M2R) := by
  rw [expKExact_mul]
  simpa using expKExact_zero

/-- `Δ` is invertible with inverse `exp(K)` in the exact projector model. -/
theorem DeltaBase_mul_inv :
    DeltaBase * expKExact 1 = (1 : M2R) := by
  unfold DeltaBase
  simpa using expKExact_mul_neg (-1)

/-- Two-sided inverse law for the base modular operator. -/
theorem DeltaBase_inv_mul :
    expKExact 1 * DeltaBase = (1 : M2R) := by
  unfold DeltaBase
  rw [expKExact_mul]
  have : (1 : ℝ) + (-1) = 0 := by ring
  rw [this]
  simpa using expKExact_zero

/-- Boundary trace invariant for `expKExact`. -/
theorem trace_expKExact_boundary (t : ℝ) :
    traceForm (expKExact t) InfoGeometry.Algebra.HypercomplexTriad.N = 0 := by
  unfold traceForm tr expKExact
  rw [N_left_eval, N_right_eval]
  norm_num [InfoGeometry.Algebra.HypercomplexTriad.N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Base logarithm remains boundary-orthogonal. -/
theorem trace_logDeltaBase_boundary :
    traceForm logDeltaBase InfoGeometry.Algebra.HypercomplexTriad.N = 0 := by
  unfold logDeltaBase traceForm tr
  rw [K_eval]
  norm_num [InfoGeometry.Algebra.HypercomplexTriad.N, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.ModularTensorInduction
