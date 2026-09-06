import InfoGeometry.Optics.ChiralCircularTransport

noncomputable section

namespace InfoGeometry.Optics.ChiralCircularTransport

open InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry

variable {Op : Type*} [Ring Op]
variable [Algebra ℂ Op]

theorem act_compressed_block
    (T : OperatorialJonesTransform Op) (p a : Op)
    (hp : T.act p = p) :
    T.act (p * a * p) = p * T.act a * p := by
  rw [act_mul, act_mul, hp]

theorem compressed_block_idempotent
    (p a : Op) (hp : p * p = p) :
    p * (p * a * p) * p = p * a * p := by
  calc
    p * (p * a * p) * p = (p * p) * a * (p * p) := by
      simp only [mul_assoc]
    _ = p * a * p := by simpa only [hp]

theorem compressed_blocks_disjoint
    (p q a b : Op) (hpq : p * q = 0) :
    (p * a * p) * (q * b * q) = 0 := by
  calc
    (p * a * p) * (q * b * q) = p * a * (p * q) * b * q := by
      simp only [mul_assoc]
    _ = 0 := by rw [hpq]; simp

theorem product_projectors_disjoint_of_left_orthogonal
    (p p' q q' : Op) (hpp' : p * p' = 0)
    (hcomm : q * p' = p' * q) :
    (p * q) * (p' * q') = 0 := by
  calc
    (p * q) * (p' * q') = p * (q * p') * q' := by
      simp only [mul_assoc]
    _ = p * (p' * q) * q' := by rw [hcomm]
    _ = 0 := by rw [← mul_assoc p p' q, hpp']; simp

theorem act_joint_compressed_block
    (T : OperatorialJonesTransform Op)
    (L : OperatorValuedCliffordJones.LoxodromicAxes Op)
    (hH : T.act L.hyperbolic = L.hyperbolic)
    (hC : T.act L.elliptic = L.elliptic)
    (hSign cSign : Bool) (a : Op) :
    T.act (L.jointProjector hSign cSign * a * L.jointProjector hSign cSign) =
      L.jointProjector hSign cSign * T.act a * L.jointProjector hSign cSign := by
  apply act_compressed_block
  exact act_loxodromic_jointProjector_of_axes T L hH hC hSign cSign

theorem act_joint_projector_resolution
    (T : OperatorialJonesTransform Op)
    (L : OperatorValuedCliffordJones.LoxodromicAxes Op)
    (hH : T.act L.hyperbolic = L.hyperbolic)
    (hC : T.act L.elliptic = L.elliptic) :
    T.act (L.jointProjector true true + L.jointProjector true false +
        L.jointProjector false true + L.jointProjector false false) =
      L.jointProjector true true + L.jointProjector true false +
        L.jointProjector false true + L.jointProjector false false := by
  rw [act_add, act_add, act_add]
  rw [act_loxodromic_jointProjector_of_axes T L hH hC,
    act_loxodromic_jointProjector_of_axes T L hH hC,
    act_loxodromic_jointProjector_of_axes T L hH hC,
    act_loxodromic_jointProjector_of_axes T L hH hC]

theorem joint_compressed_block_idempotent
    (L : OperatorValuedCliffordJones.LoxodromicAxes Op)
    (hSign cSign : Bool) (a : Op) :
    L.jointProjector hSign cSign *
        (L.jointProjector hSign cSign * a * L.jointProjector hSign cSign) *
      L.jointProjector hSign cSign =
      L.jointProjector hSign cSign * a * L.jointProjector hSign cSign := by
  apply compressed_block_idempotent
  exact L.jointProjector_idempotent hSign cSign

end InfoGeometry.Optics.ChiralCircularTransport
