/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.CantorTransferOperator

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.CantorTransferOperator

/-! A finite, kernel-checked synthesis of the balanced Cantor transfer lane. -/
theorem cantor_transfer_operator_canonical_capstone {n : ℕ}
    (f g : CylinderFunction (n + 1))
    (c : ℝ) (x : Fin n → Bool) (σ : ℝ)
    (h_casimir : σ - 1 / 2 = 0) :
    (transferOperator (1 / 2) (1 / 2) (fun w => f w + g w) x =
      transferOperator (1 / 2) (1 / 2) f x +
        transferOperator (1 / 2) (1 / 2) g x) ∧
    (transferOperator (1 / 2) (1 / 2) (fun w => c * f w) x =
      c * transferOperator (1 / 2) (1 / 2) f x) ∧
    (transferOperator (1 / 2) (1 / 2) (fun _ => 1) x = 1) ∧
    (σ = 1 / 2) := by
  exact ⟨transferOperator_add _ _ f g x,
    transferOperator_smul _ _ c f x,
    transferOperator_uniform_preserves_one x,
    critical_line_from_transfer_fixed_point σ h_casimir⟩

end InfoGeometry.Canonical
