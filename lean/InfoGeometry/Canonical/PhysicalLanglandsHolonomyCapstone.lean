/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

/-- Canonical identity-model projection of the operator-level Langlands witness. -/
theorem physical_langlands_holonomy_canonical_capstone
    (State Loop Scalar : Type*)
    (W : WilsonReadoutDatum State Loop Scalar) :
    let T : THooftReadoutDatum State Loop Scalar := ⟨W.wilson⟩
    let D : LanglandsDualPair State State Loop Loop := ⟨id, id⟩
    let K : KWPhysicalDualityWitness State State Loop Loop Scalar W T D :=
      ⟨fun γ s => rfl⟩
    (∀ (γ : Loop) (s : State),
      W.wilson γ s = T.thooft (D.loopDual γ) (D.stateDual s)) ∧
    (∀ (γ : Loop) (s : State), K.wilson_readout_eq_dual_thooft γ s = rfl) := by
  dsimp
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end InfoGeometry.Canonical
