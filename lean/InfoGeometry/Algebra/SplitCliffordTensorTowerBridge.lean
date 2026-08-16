import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.SplitCliffordTensorTowerBridge

/-- Finite scalar data satisfying the displayed Cl(1,1) multiplication
    relations. -/
structure Cl11Atom (R : Type*) [Ring R] where
  e1 : R
  e2 : R
  e1_sq : e1 * e1 = 1
  e2_sq : e2 * e2 = -1
  anticomm : e1 * e2 + e2 * e1 = 0

namespace Cl11Atom

variable {R : Type*} [Ring R] (atom : Cl11Atom R)

/-- Product readout `e1 * e2`. -/
def cptOperator : R := atom.e1 * atom.e2

/-- The product readout squares to `1` under the supplied relations. -/
theorem cptOperator_squared : atom.cptOperator * atom.cptOperator = 1 := by
  dsimp [cptOperator]
  have h_anticomm : atom.e2 * atom.e1 = - (atom.e1 * atom.e2) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact atom.anticomm)
  calc atom.e1 * atom.e2 * (atom.e1 * atom.e2)
    _ = atom.e1 * (atom.e2 * atom.e1) * atom.e2 := by noncomm_ring
    _ = atom.e1 * (- (atom.e1 * atom.e2)) * atom.e2 := by rw [h_anticomm]
    _ = - (atom.e1 * atom.e1 * (atom.e2 * atom.e2)) := by noncomm_ring
    _ = - (1 * (-1)) := by rw [atom.e1_sq, atom.e2_sq]
    _ = 1 := by simp

end Cl11Atom

/-- A finite integer signature function with five `+1` and five `-1`
    entries. -/
def cl55Metric (i : Fin 10) : ℤ :=
  if i.val < 5 then 1 else -1

/-- The finite signature sum is zero.  This is an arithmetic readout, not a
    Pin-group or anomaly-cancellation theorem. -/
theorem pin55_metric_trace_neutrality :
    (Finset.univ : Finset (Fin 10)).sum cl55Metric = 0 := by
  norm_num [cl55Metric, Fin.sum_univ_succ]

/-- The displayed arithmetic value `2^(2*5) = 1024`.  No Clifford-algebra
    dimension isomorphism is constructed by this theorem. -/
theorem cl55_dimension : (2 : ℕ)^(2 * 5) = 1024 := by
  norm_num

/-- The scalar dimension recurrence used by the finite tower calculation. -/
def splitCliffordTensorEmbedding (dimN : ℕ) : ℕ :=
  dimN * 4

/-- Five finite applications of the scalar recurrence give `4^5 = 1024`.
    This does not construct an infinite UHF limit. -/
theorem tensor_tower_5_step_growth :
    (((1 * 4) * 4) * 4) * 4 * 4 = 1024 := by
  rfl

end InfoGeometry.Algebra.SplitCliffordTensorTowerBridge
