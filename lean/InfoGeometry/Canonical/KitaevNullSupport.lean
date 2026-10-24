/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevNullPartner

/-! The normalized native null pair has proper active support in the
four-dimensional state space. Its action is expressed by the Dirac bras. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevNullSupport
open Matrix KitaevConcreteBoundary KitaevNullPartner DiracNullPeirce
open ReflexiveNilpotentFlows KitaevSpinorSolder
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

def active : CARMajoranaFiniteBridge.ChainOp :=
  support (solder twoSiteKreinData.eta seed seed) (solder twoSiteKreinData.eta partner partner)

theorem active_expansion : active =
    solder twoSiteKreinData.eta seed partner + solder twoSiteKreinData.eta partner seed := by
  unfold active support
  rw [solder_product, solder_product, seed_partner, partner_seed, one_smul, one_smul]

theorem active_action (z : (Fin 2 × Fin 2) → ℂ) : active *ᵥ z =
    (SpinorialCore.Krein.metricDual twoSiteKreinData.eta partner z) • seed +
    (SpinorialCore.Krein.metricDual twoSiteKreinData.eta seed z) • partner := by
  rw [active_expansion, Matrix.add_mulVec, solder_action, solder_action]

theorem active_idempotent : active * active = active :=
  support_sq native_reflexive_pair.1 native_reflexive_pair.2.1
    native_reflexive_pair.2.2.1 native_reflexive_pair.2.2.2

theorem active_trace : Matrix.trace active = 2 :=
  normalized_support_trace _ _ _ seed_partner partner_seed

theorem active_ne_one : active ≠ 1 := by
  intro h
  have ht := active_trace
  rw [h, Matrix.trace_one] at ht
  norm_num at ht

theorem active_fixes_null_pair : active *ᵥ seed = seed ∧ active *ᵥ partner = partner := by
  simp only [active_action]
  change (SpinorialCore.Krein.pairing twoSiteKreinData.eta partner seed) • seed +
    (SpinorialCore.Krein.pairing twoSiteKreinData.eta seed seed) • partner = seed ∧
    (SpinorialCore.Krein.pairing twoSiteKreinData.eta partner partner) • seed +
    (SpinorialCore.Krein.pairing twoSiteKreinData.eta seed partner) • partner = partner
  simp only [seed_partner, partner_seed, seed_null, partner_null,
    one_smul, zero_smul, zero_add, add_zero, and_self]

end InfoGeometry.Canonical.KitaevNullSupport
