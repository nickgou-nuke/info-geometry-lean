import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.FenchelExpLogScalar
import InfoGeometry.Canonical.ModularTensorInduction
import InfoGeometry.Canonical.ModularSL2R
import InfoGeometry.Canonical.ModularLorentzBoost

/-!
# InfoGeometry.Canonical.TomitaBregmanDuality

Finite operatorial Bregman readout on `M₂(ℝ)`.

Define the lifted finite operator
`B = Δ - 1 - logΔ`
with `Δ = DeltaBase` and `logΔ = logDeltaBase`.
We prove:
* `B` is diagonal (explicitly evaluated),
* `traceForm B N = 0`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.TomitaBregmanDuality

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.FenchelExpLogScalar
open InfoGeometry.Canonical.ModularTensorInduction
open InfoGeometry.Canonical.ModularSL2R

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Finite lifted Tomita-Bregman operator: `Δ - 1 - logΔ`. -/
noncomputable def TomitaBregmanOp : M2R :=
  DeltaBase - (1 : M2R) - logDeltaBase

/-- Explicit diagonal form of `TomitaBregmanOp`. -/
theorem tomita_bregman_diagonal :
    TomitaBregmanOp = !![Real.exp (-1), 0; 0, Real.exp 1 - 1 - 1] := by
  unfold TomitaBregmanOp DeltaBase logDeltaBase
  rw [expKExact_eval, InfoGeometry.Canonical.ModularLorentzBoost.K_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/-- Boundary trace regularization for the lifted Bregman operator. -/
theorem trace_tomita_bregman_boundary_invariant :
    traceForm TomitaBregmanOp N = 0 := by
  rw [tomita_bregman_diagonal]
  unfold traceForm tr
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- `(0,0)` channel equals the scalar Bregman seed `exp(-1) - 1 - (-1) = exp(-1)`. -/
theorem tomita_bregman_channel00 :
    TomitaBregmanOp 0 0 = Real.exp (-1) := by
  rw [tomita_bregman_diagonal]
  norm_num

/-- `(1,1)` channel equals the scalar Bregman seed `exp(1) - 1 - 1`. -/
theorem tomita_bregman_channel11 :
    TomitaBregmanOp 1 1 = Real.exp 1 - 1 - 1 := by
  rw [tomita_bregman_diagonal]
  norm_num

/-- The `(0,0)` Bregman channel is strictly positive. -/
theorem tomita_bregman_channel00_pos :
    0 < TomitaBregmanOp 0 0 := by
  rw [tomita_bregman_channel00]
  exact Real.exp_pos (-1)

/-- The `(1,1)` Bregman channel is strictly positive (`e - 2 > 0`). -/
theorem tomita_bregman_channel11_pos :
    0 < TomitaBregmanOp 1 1 := by
  rw [tomita_bregman_channel11]
  nlinarith [Real.exp_one_gt_two]

/-- Both diagonal channels are nonnegative. -/
theorem tomita_bregman_diag_nonneg :
    0 ≤ TomitaBregmanOp 0 0 ∧ 0 ≤ TomitaBregmanOp 1 1 := by
  constructor
  · exact le_of_lt tomita_bregman_channel00_pos
  · exact le_of_lt tomita_bregman_channel11_pos

/-- `(0,0)` channel matches the scalar primal Bregman seed at `x=-1`, `x₀=0`. -/
theorem tomita_channel00_eq_scalar_bregman :
    TomitaBregmanOp 0 0 = bregmanPrimal (-1) 0 := by
  rw [tomita_bregman_channel00, bregmanPrimal_closed]
  norm_num

/-- `(1,1)` channel matches the scalar primal Bregman seed at `x=1`, `x₀=0`. -/
theorem tomita_channel11_eq_scalar_bregman :
    TomitaBregmanOp 1 1 = bregmanPrimal 1 0 := by
  rw [tomita_bregman_channel11, bregmanPrimal_closed]
  norm_num

end InfoGeometry.Canonical.TomitaBregmanDuality
