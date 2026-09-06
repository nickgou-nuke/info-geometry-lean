import Mathlib
import InfoGeometry.Topology.SymbolicLatentFlowQuotient

namespace InfoGeometry.Topology

/-!
# Homeomorphisms induced by a descended symbolic latent flow

The quotient owner supplies a continuous action and its additive law.  The
negative-time action is therefore its continuous inverse.  This file lifts
the pointwise quotient flow to `Homeomorph`, without adding a claim about a
particular quotient topology beyond the continuity already stored in the
owner.
-/

def SymbolicLatentFlowQuotient.actHomeomorph
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (t : ℝ) : Q ≃ₜ Q where
  toFun := K.act t
  invFun := K.act (-t)
  left_inv := by
    intro q
    calc
      K.act (-t) (K.act t q) = K.act (-t + t) q :=
        (K.act_add (-t) t q).symm
      _ = q := by rw [neg_add_cancel, K.act_zero]
  right_inv := by
    intro q
    calc
      K.act t (K.act (-t) q) = K.act (t + -t) q :=
        (K.act_add t (-t) q).symm
      _ = q := by rw [add_neg_cancel, K.act_zero]
  continuous_toFun := by
    exact K.continuous_act.comp
      (continuous_const.prodMk continuous_id)
  continuous_invFun := by
    exact K.continuous_act.comp
      (continuous_const.prodMk continuous_id)

@[simp] theorem SymbolicLatentFlowQuotient.actHomeomorph_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (t : ℝ) (q : Q) :
    K.actHomeomorph t q = K.act t q := rfl

theorem SymbolicLatentFlowQuotient.actHomeomorph_add_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s t : ℝ) (q : Q) :
    K.actHomeomorph (s + t) q =
      K.actHomeomorph s (K.actHomeomorph t q) := by
  simpa only [SymbolicLatentFlowQuotient.actHomeomorph_apply] using
    K.act_add s t q

theorem SymbolicLatentFlowQuotient.actHomeomorph_zero_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    K.actHomeomorph 0 q = q := by
  simpa only [SymbolicLatentFlowQuotient.actHomeomorph_apply] using
    K.act_zero q

end InfoGeometry.Topology
