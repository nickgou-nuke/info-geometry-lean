/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FiniteSoftmax

/-!
# Finite log-domain Sinkhorn iterations

A new representation of alternating log potentials, not a replacement for the
existing SinkhornFoundation scaling owner. Each final column is identified
with the existing FiniteSoftmax.weight at temperature one. Finite iteration
proves column normalization only, not membership in the Birkhoff polytope.
The trifactor equality holds at every step, including step zero.
-/

namespace InfoGeometry.Routing.FiniteLogSinkhorn

open scoped BigOperators
noncomputable section
variable {K : Type*} [Fintype K]

/-- Finite log partition, using the existing softmax partition owner. -/
def logsumexp (f : K → ℝ) : ℝ := Real.log (FiniteSoftmax.partitionZ f 1)

/-- Negative log normalization gives exactly the existing finite softmax. -/
theorem exp_sub_logsumexp [Nonempty K] (f : K → ℝ) (k : K) :
    Real.exp (f k - logsumexp f) = FiniteSoftmax.weight f 1 k := by
  rw [Real.exp_sub, logsumexp,
    Real.exp_log (FiniteSoftmax.partitionZ_pos f 1)]
  simp only [FiniteSoftmax.weight, div_one]

/-- Alternating row and column log potentials. -/
def sinkhornPotentials (logS : Matrix K K ℝ) : ℕ → (K → ℝ) × (K → ℝ)
  | 0 => (0, 0)
  | n + 1 =>
      let uv := sinkhornPotentials logS n
      let u' := fun k => -logsumexp (fun l => logS k l + uv.2 l)
      let v' := fun l => -logsumexp (fun k => logS k l + u' k)
      (u', v')

/-- Balanced potential gauge. Meaningful nonempty-channel use is explicit. -/
def sinkhornGaugeShift (uv : (K → ℝ) × (K → ℝ)) : ℝ :=
  (2 * (Fintype.card K : ℝ))⁻¹ * ∑ k, (uv.1 k - uv.2 k)

def sinkhornMatrix (T : ℕ) (logS : Matrix K K ℝ) : Matrix K K ℝ :=
  let uv := sinkhornPotentials logS T
  fun k l => Real.exp (logS k l + uv.1 k + uv.2 l)

def sinkhornShapeGain (T : ℕ) (logS : Matrix K K ℝ) : K → ℝ :=
  let uv := sinkhornPotentials logS T
  fun k => Real.exp (-uv.1 k + sinkhornGaugeShift uv)

def sinkhornDetGain (T : ℕ) (logS : Matrix K K ℝ) : K → ℝ :=
  let uv := sinkhornPotentials logS T
  fun l => Real.exp (-uv.2 l - sinkhornGaugeShift uv)

theorem sinkhornMatrix_pos (T : ℕ) (logS : Matrix K K ℝ) (k l : K) :
    0 < sinkhornMatrix T logS k l := Real.exp_pos _

theorem sinkhornDetGain_pos (T : ℕ) (logS : Matrix K K ℝ) (l : K) :
    0 < sinkhornDetGain T logS l := Real.exp_pos _

theorem sinkhornShapeGain_pos (T : ℕ) (logS : Matrix K K ℝ) (k : K) :
    0 < sinkhornShapeGain T logS k := Real.exp_pos _

/-- Full columns are normalized softmax rows after the final column update. -/
theorem sinkhornMatrix_succ_eq_softmax [Nonempty K]
    (T : ℕ) (logS : Matrix K K ℝ) (k l : K) :
    sinkhornMatrix (T + 1) logS k l =
      FiniteSoftmax.weight
        (fun r => logS r l -
          logsumexp (fun s => logS r s + (sinkhornPotentials logS T).2 s)) 1 k := by
  simpa only [sinkhornMatrix, sinkhornPotentials, sub_eq_add_neg] using
    exp_sub_logsumexp
      (fun r => logS r l -
        logsumexp (fun s => logS r s + (sinkhornPotentials logS T).2 s)) k

theorem sinkhorn_trifactor (T : ℕ) (logS : Matrix K K ℝ) (k l : K) :
    sinkhornShapeGain T logS k * sinkhornMatrix T logS k l *
      sinkhornDetGain T logS l = Real.exp (logS k l) := by
  unfold sinkhornShapeGain sinkhornMatrix sinkhornDetGain
  dsimp only
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem sinkhorn_col_sum [Nonempty K] (T : ℕ) (logS : Matrix K K ℝ) (l : K) :
    ∑ k, sinkhornMatrix (T + 1) logS k l = 1 := by
  simp_rw [sinkhornMatrix_succ_eq_softmax]
  exact FiniteSoftmax.weight_sum_one _ _

end
end InfoGeometry.Routing.FiniteLogSinkhorn
