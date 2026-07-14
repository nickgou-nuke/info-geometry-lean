import InfoGeometry.Algebra.CARFockBridge_withproofs

/-!
# CAR/Fock bridge

Checked finite CAR/Fock facts are owned by `CARFockBridge_withproofs` and
`FiniteSingleModeCAR`.  This module is a compatibility import with no proof debt.
-/

noncomputable section

namespace CARFockBridge

open InfoGeometry.Algebra.CARFockBridgeWithProofs
open InfoGeometry.Algebra.FiniteSingleModeCAR
open InfoGeometry.Arithmetic.PrimonFockTraceFinite

/-- Compatibility export: one-mode CAR laws. -/
theorem one_mode_car_laws :
    opComp ann ann = (fun _ : OneModeVec => 0) ∧
    opComp cre cre = (fun _ : OneModeVec => 0) ∧
    opAdd (opComp ann cre) (opComp cre ann) = idOp := by
  exact one_mode_car_packet

/-- Compatibility export: finite many-mode diagonal trace factorization. -/
theorem finite_trace_factorization (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    fockTraceExp n ε β = ∏ i : Fin n, (1 + localBoltzmann (ε i) β) := by
  exact finite_many_mode_trace_packet n ε β

end CARFockBridge
