import InfoGeometry.Topology.D4StarColimitDynamics

namespace InfoGeometry.Topology.ColimitDynamics

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable (D : TopologicalDiscreteFlowSystem (J := J))
variable (C : Cocone D.carrier)
variable (hC : IsColimit C)

/-!
# Invertibility of the induced colimit flow

The stage-wise additive law makes the `-t` time slice a two-sided inverse of
the `t` slice after passage to the colimit.  This is a topological action
theorem, not a modular or KMS theorem.
-/

theorem colimitEndomorphism_comp_neg (t : ℤ) :
    colimitEndomorphism D C hC t ≫
        colimitEndomorphism D C hC (-t) = 𝟙 C.pt := by
  rw [← colimitEndomorphism_add D C hC (-t) t, neg_add_cancel,
    colimitEndomorphism_zero]

theorem colimitEndomorphism_neg_comp (t : ℤ) :
    colimitEndomorphism D C hC (-t) ≫
        colimitEndomorphism D C hC t = 𝟙 C.pt := by
  rw [← colimitEndomorphism_add D C hC t (-t), add_neg_cancel,
    colimitEndomorphism_zero]

end InfoGeometry.Topology.ColimitDynamics
