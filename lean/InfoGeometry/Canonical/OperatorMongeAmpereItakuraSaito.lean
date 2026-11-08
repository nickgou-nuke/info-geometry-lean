import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix Real

namespace InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito

noncomputable section

/-!
# Finite operator Monge--Ampere and Itakura--Saito channels

This owner is a diagonal real `2 x 2` calculation.  The determinant channel
records the scalar volume parameter, while the trace of the operator defect
retains the split affinity.  No analytic matrix logarithm or physical model is
introduced.
-/

def gamma : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def trace2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A 0 0 + A 1 1

def det2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

def surprisal (κ a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • 1 + a • gamma

noncomputable def delta (κ a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp (-(κ + a)), 0; 0, Real.exp (-(κ - a))]

noncomputable def operatorDefect (κ a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  delta κ a - 1 + surprisal κ a

/-- Isotropic volume contribution to the finite defect trace. -/
noncomputable def volumeDefect (κ : ℝ) : ℝ :=
  2 * (Real.exp (-κ) - 1 + κ)

/-- Volume-weighted traceless affinity contribution to the finite defect trace. -/
noncomputable def shapeDefect (κ a : ℝ) : ℝ :=
  2 * Real.exp (-κ) * (Real.cosh a - 1)

theorem volumeDefect_nonneg (κ : ℝ) : 0 ≤ volumeDefect κ := by
  unfold volumeDefect
  have h := add_one_le_exp (-κ)
  linarith

theorem shapeDefect_nonneg (κ a : ℝ) : 0 ≤ shapeDefect κ a := by
  unfold shapeDefect
  have hexp : 0 ≤ Real.exp (-κ) := le_of_lt (Real.exp_pos _)
  have hcosh : 0 ≤ Real.cosh a - 1 := sub_nonneg.mpr (Real.one_le_cosh a)
  exact mul_nonneg (mul_nonneg (by norm_num) hexp) hcosh

lemma surprisal_val (κ a : ℝ) :
    surprisal κ a = !![κ + a, 0; 0, κ - a] := by
  ext i j
  unfold surprisal gamma
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem det_delta (κ a : ℝ) :
    det2 (delta κ a) = Real.exp (-2 * κ) := by
  unfold det2 delta
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, head_cons, tail_cons]
  rw [← Real.exp_add]
  congr 1
  ring

theorem trace_surprisal (κ a : ℝ) :
    trace2 (surprisal κ a) = 2 * κ := by
  rw [surprisal_val]
  unfold trace2
  change (κ + a) + (κ - a) = 2 * κ
  ring

theorem monge_ampere_channel (κ a : ℝ) :
    -Real.log (det2 (delta κ a)) = trace2 (surprisal κ a) := by
  rw [det_delta, trace_surprisal, Real.log_exp]
  ring

theorem unimodular_monge_ampere_blindness (a : ℝ) :
    -Real.log (det2 (delta 0 a)) = 0 := by
  rw [monge_ampere_channel, trace_surprisal]
  ring

theorem defect_trace (κ a : ℝ) :
    trace2 (operatorDefect κ a) =
      2 * Real.exp (-κ) * Real.cosh a - 2 + 2 * κ := by
  unfold operatorDefect trace2 delta
  rw [surprisal_val]
  change
    (Real.exp (-(κ + a)) - 1 + (κ + a)) +
        (Real.exp (-(κ - a)) - 1 + (κ - a)) =
      2 * Real.exp (-κ) * Real.cosh a - 2 + 2 * κ
  have h_cosh : Real.cosh a = (Real.exp a + Real.exp (-a)) / 2 :=
    Real.cosh_eq a
  have h_exp1 : Real.exp (-(κ + a)) =
      Real.exp (-κ) * Real.exp (-a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h_exp2 : Real.exp (-(κ - a)) =
      Real.exp (-κ) * Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_exp1, h_exp2, h_cosh]
  ring

theorem unimodular_defect_trace (a : ℝ) :
    trace2 (operatorDefect 0 a) = 2 * (Real.cosh a - 1) := by
  rw [defect_trace]
  simp only [neg_zero, Real.exp_zero, mul_one]
  ring

/-!
The defect separates into an isotropic volume contribution and a
volume-weighted traceless affinity contribution.
-/
theorem defect_trace_volume_shape_split (κ a : ℝ) :
    trace2 (operatorDefect κ a) =
      2 * (Real.exp (-κ) - 1 + κ) +
        2 * Real.exp (-κ) * (Real.cosh a - 1) := by
  rw [defect_trace]
  ring

theorem defect_trace_eq_volumeDefect_add_shapeDefect (κ a : ℝ) :
    trace2 (operatorDefect κ a) = volumeDefect κ + shapeDefect κ a := by
  rw [defect_trace]
  unfold volumeDefect shapeDefect
  ring

theorem defect_trace_nonneg (κ a : ℝ) :
    0 ≤ trace2 (operatorDefect κ a) := by
  rw [defect_trace_eq_volumeDefect_add_shapeDefect]
  exact add_nonneg (volumeDefect_nonneg κ) (shapeDefect_nonneg κ a)

end

end InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito
