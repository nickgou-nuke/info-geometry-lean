import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Statistical curvature and Zorn standard derivations

This file records the operator-level comparison only.  It does not identify a
Levi--Civita curvature vector with the Zorn associator.  A concrete geometric
model must supply the curvature representation and the tangent-to-Zorn map.
-/

namespace InfoGeometry.Algebra

noncomputable section

structure StatisticalZornDerivationSoldering
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (R0 : T → T → Module.End ℝ T) where
  tangentToZorn : T →ₗ[ℝ] ZornVectorMatrix ℝ
  curvatureRep : Module.End ℝ T →ₗ[ℝ] Module.End ℝ (ZornVectorMatrix ℝ)
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  curvatureRep_eq : ∀ X Y,
    curvatureRep (R0 X Y) =
      scale • (zornStanDerivation
        (tangentToZorn X) (tangentToZorn Y)).toLinearMap

theorem StatisticalZornDerivationSoldering.curvatureRep_apply
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → Module.End ℝ T}
    (B : StatisticalZornDerivationSoldering R0)
    (X Y Z : T) :
    B.curvatureRep (R0 X Y) (B.tangentToZorn Z) =
      B.scale • zornStanDerivation
        (B.tangentToZorn X) (B.tangentToZorn Y) (B.tangentToZorn Z) := by
  rw [B.curvatureRep_eq X Y]
  rfl

theorem StatisticalZornDerivationSoldering.curvatureRep_apply_normal_form
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → Module.End ℝ T}
    (B : StatisticalZornDerivationSoldering R0)
    (X Y Z : T) :
    B.curvatureRep (R0 X Y) (B.tangentToZorn Z) =
      B.scale • (((B.tangentToZorn X * B.tangentToZorn Y -
          B.tangentToZorn Y * B.tangentToZorn X) * B.tangentToZorn Z -
        B.tangentToZorn Z * (B.tangentToZorn X * B.tangentToZorn Y -
          B.tangentToZorn Y * B.tangentToZorn X)) -
        3 • _root_.associator (B.tangentToZorn X)
          (B.tangentToZorn Y) (B.tangentToZorn Z)) := by
  rw [B.curvatureRep_apply]
  rw [zornStanDerivation_apply_normal_form]

end
end InfoGeometry.Algebra
