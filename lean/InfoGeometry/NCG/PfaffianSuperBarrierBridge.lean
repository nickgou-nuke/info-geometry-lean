import InfoGeometry.Volume.PfaffianGeneral
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.NCG.PfaffianSuperBarrierBridge

open scoped BigOperators
open InfoGeometry.Volume.PfaffianGeneral

/-- Positive Pfaffian component of the canonical real block-skew family. -/
def PositivePfaffianBlock (n : ℕ) (a : Fin n → ℝ) : Prop :=
  0 < pfaffianBlock n a

/-- Entrywise positivity is sufficient for positivity of the block Pfaffian. -/
theorem positivePfaffianBlock_of_entrywise_pos
    (n : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    PositivePfaffianBlock n a := by
  unfold PositivePfaffianBlock pfaffianBlock
  exact Finset.prod_pos fun i _ => ha i

/-- Determinant logarithmic barrier of the canonical block-skew matrix. -/
def skewDetLogBarrier (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  -Real.log ((blockSkewMatrix n a).det)

/-- Pfaffian logarithmic barrier on the positive Pfaffian component. -/
def pfaffianLogBarrier (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  -Real.log (pfaffianBlock n a)

/--
For canonical block-skew matrices with positive Pfaffian,
`-log det = 2 * (-log Pf)`.

This is the exact finite square-root relation underlying the Majorana versus
Dirac determinant readout.  No functional-integral or anomaly statement is
used.
-/
theorem skewDetLogBarrier_eq_two_mul_pfaffianLogBarrier
    (n : ℕ) (a : Fin n → ℝ)
    (hpf : PositivePfaffianBlock n a) :
    skewDetLogBarrier n a = 2 * pfaffianLogBarrier n a := by
  unfold skewDetLogBarrier pfaffianLogBarrier PositivePfaffianBlock at *
  rw [← pfaffian_sq_eq_det_general]
  rw [pow_two, Real.log_mul hpf.ne' hpf.ne']
  ring

/-- Equal unit Pfaffian gives zero determinant and Pfaffian barriers. -/
theorem unit_pfaffian_zero_barriers
    (n : ℕ) (a : Fin n → ℝ)
    (hpf : pfaffianBlock n a = 1) :
    pfaffianLogBarrier n a = 0 ∧ skewDetLogBarrier n a = 0 := by
  constructor
  · simp [pfaffianLogBarrier, hpf]
  · rw [skewDetLogBarrier, ← pfaffian_sq_eq_det_general, hpf]
    simp

end InfoGeometry.NCG.PfaffianSuperBarrierBridge

