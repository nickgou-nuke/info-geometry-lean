import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact algebraic core of the upstream photonic SOI model.  The structure
 records two rates and a passive upper bound; no topological-protection or
 device-performance claim is encoded. -/

namespace InfoGeometry.Canonical.PhotonicSOIBridge

structure Model where
  gamma : ℝ
  kappa : ℝ
  passive : kappa ≤ gamma

def parityRate (p : Model) : ℝ := p.gamma - p.kappa

def bulkRate (p : Model) : ℝ := p.gamma + p.kappa

theorem parityRate_nonneg (p : Model) : 0 ≤ parityRate p := by
  dsimp [parityRate]
  linarith [p.passive]

theorem parityRate_lt_bulkRate (p : Model) (h : 0 < p.kappa) :
    parityRate p < bulkRate p := by
  dsimp [parityRate, bulkRate]
  linarith

theorem parityRate_eq_zero_iff (p : Model) :
    parityRate p = 0 ↔ p.kappa = p.gamma := by
  dsimp [parityRate]
  constructor <;> intro h <;> linarith

theorem bulkRate_eq_parityRate_add_two_kappa (p : Model) :
    bulkRate p = parityRate p + 2 * p.kappa := by
  dsimp [bulkRate, parityRate]
  ring

end InfoGeometry.Canonical.PhotonicSOIBridge
