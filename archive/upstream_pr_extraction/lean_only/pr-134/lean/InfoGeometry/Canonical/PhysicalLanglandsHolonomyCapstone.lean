/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

/-- Canonical projection capstone for Kapustin-Witten physical Langlands holonomy duality. -/
theorem physical_langlands_holonomy_canonical_capstone
    (State Loop Scalar : Type*)
    (W : WilsonReadoutDatum State Loop Scalar) :
    let K := KWPhysicalDualityWitness.ofSelf State Loop Scalar W
    -- 1. Wilson readout equals dual 't Hooft readout
    (∀ (γ : Loop) (s : State), W.wilson γ s = (⟨W.wilson⟩ : THooftReadoutDatum State Loop Scalar).thooft ((⟨id, id⟩ : LanglandsDualPair State State Loop Loop).loopDual γ) ((⟨id, id⟩ : LanglandsDualPair State State Loop Loop).stateDual s)) ∧
    -- 2. Direct readback
    (∀ (γ : Loop) (s : State), K.wilson_readout_eq_dual_thooft γ s = rfl) := by
  intro K
  exact ⟨
    fun γ s => K.wilson_eq_thooft_dual γ s,
    fun γ s => rfl
  ⟩

end InfoGeometry.Canonical
