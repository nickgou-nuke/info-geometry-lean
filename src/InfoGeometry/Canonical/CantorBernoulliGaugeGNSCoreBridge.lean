import InfoGeometry.Canonical.GNSState
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Finite gauge kernel / cylinder-GNS bridge

This file identifies the already proved real cylinder weight used by the
finite `GNSState` owner with the diagonal of the complex canonical gauge
word kernel.  It does not claim a positive functional on the completed
concrete C*-algebra; it only removes a duplicated finite weight boundary.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.CantorBernoulliGaugeGNSCoreBridge

open InfoGeometry.Canonical.GNSState
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-- The complex gauge-kernel diagonal is the complexification of the
finite-cylinder GNS weight. -/
theorem canonicalGaugeState_diag_eq_gnsCylinderWeight (w : List Bool) :
    canonicalGaugeState w w = (gnsCylinderWeight w : ℂ) := by
  rw [canonicalGaugeState_proj]
  simp [gnsCylinderWeight]

/-- Prefixing a branch halves the canonical complex gauge weight. -/
theorem canonicalGaugeState_cons_diag (b : Bool) (w : List Bool) :
    canonicalGaugeState (b :: w) (b :: w) =
  (1 / 2 : ℂ) * canonicalGaugeState w w := by
  rw [canonicalGaugeState_diag_eq_gnsCylinderWeight (b :: w),
    canonicalGaugeState_diag_eq_gnsCylinderWeight w]
  simp [gnsCylinderWeight, pow_succ, mul_comm]

end InfoGeometry.Canonical.CantorBernoulliGaugeGNSCoreBridge
