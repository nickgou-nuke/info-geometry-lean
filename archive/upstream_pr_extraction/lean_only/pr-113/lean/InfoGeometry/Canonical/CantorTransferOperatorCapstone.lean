/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.CantorTransferOperator

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.CantorTransferOperator

/-- Canonical projection capstone for Cantor Transfer Operator module. -/
theorem cantor_transfer_operator_canonical_capstone {n : ℕ}
    (f g : CylinderFunction (n + 1))
    (c : ℝ) (x : Fin n → Bool) (σ : ℝ) (h_casimir : σ - 1 / 2 = 0) :
    (transferOperator (1 / 2) (1 / 2) (fun w => f w + g w) x =
      transferOperator (1 / 2) (1 / 2) f x + transferOperator (1 / 2) (1 / 2) g x) ∧
    (transferOperator (1 / 2) (1 / 2) (fun w => c * f w) x =
      c * transferOperator (1 / 2) (1 / 2) f x) ∧
    (transferOperator (1 / 2) (1 / 2) (fun _ => 1) x = 1) ∧
    (σ = 1 / 2) :=
  grand_cantor_transfer_synthesis f g c x σ h_casimir

end InfoGeometry.Canonical
