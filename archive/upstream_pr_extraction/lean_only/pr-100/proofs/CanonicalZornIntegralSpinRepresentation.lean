import proofs.CanonicalZornIntegralSpinSubgroup

/-!
# Integral spin representation on Zorn coordinates

The arithmetic spin subgroup already preserves the embedded integral Zorn
lattice.  Here its selected action is proved `ℤ`-linear and bundled as a
genuine representation in the integral general linear group.  The defining
square with the real `Spin(4,4)` vector action commutes exactly.
-/

noncomputable section

namespace CanonicalZornIntegralSpinRepresentation

open IntegralZornII44Bridge
open CanonicalZornRealSpin44
open CanonicalZornRealComplexSpinBaseChange
open CanonicalZornIntegralSpinTrialityClosure
open CanonicalZornIntegralSpinSubgroup

theorem integralZornToRealSplit44_add (X Y : IntegralZorn) :
    integralZornToRealSplit44 (X + Y) =
      integralZornToRealSplit44 X + integralZornToRealSplit44 Y := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [integralZornToRealSplit44,
      CanonicalZornProjectiveTKKBridge.coreZornToPAC44,
      integralToCoreZorn, IntegralZorn.a, IntegralZorn.u,
      IntegralZorn.v, IntegralZorn.b] <;> ring

theorem integralZornToRealSplit44_smul
    (n : ℤ) (X : IntegralZorn) :
    integralZornToRealSplit44 (n • X) =
      (n : ℝ) • integralZornToRealSplit44 X := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [integralZornToRealSplit44,
      CanonicalZornProjectiveTKKBridge.coreZornToPAC44,
      integralToCoreZorn, IntegralZorn.a, IntegralZorn.u,
      IntegralZorn.v, IntegralZorn.b] <;> ring

theorem integralSpinAction_add
    (g : integralSpin44) (X Y : IntegralZorn) :
    integralSpinAction g (X + Y) =
      integralSpinAction g X + integralSpinAction g Y := by
  apply integralZornToRealSplit44_injective
  rw [← integralSpinAction_spec, integralZornToRealSplit44_add]
  rw [(realSpinVectorLinear g.1).map_add]
  rw [integralSpinAction_spec, integralSpinAction_spec,
    integralZornToRealSplit44_add]

theorem integralSpinAction_smul
    (g : integralSpin44) (n : ℤ) (X : IntegralZorn) :
    integralSpinAction g (n • X) = n • integralSpinAction g X := by
  apply integralZornToRealSplit44_injective
  rw [← integralSpinAction_spec, integralZornToRealSplit44_smul]
  rw [(realSpinVectorLinear g.1).map_smul]
  rw [integralSpinAction_spec, integralZornToRealSplit44_smul]

/-- The arithmetic spin action as an integral linear endomorphism. -/
def integralSpinLinear (g : integralSpin44) :
    Module.End ℤ IntegralZorn where
  toFun := integralSpinAction g
  map_add' := integralSpinAction_add g
  map_smul' := integralSpinAction_smul g

theorem integralSpinLinear_one : integralSpinLinear 1 = 1 := by
  apply LinearMap.ext
  exact integralSpinAction_one

theorem integralSpinLinear_mul (g h : integralSpin44) :
    integralSpinLinear (g * h) = integralSpinLinear g * integralSpinLinear h := by
  apply LinearMap.ext
  exact integralSpinAction_mul g h

/-- Genuine integral eight-dimensional representation of the
lattice-preserving real spin subgroup. -/
def integralSpinRepresentation :
    integralSpin44 →* LinearMap.GeneralLinearGroup ℤ IntegralZorn where
  toFun g :=
    { val := integralSpinLinear g
      inv := integralSpinLinear g⁻¹
      val_inv := by
        rw [← integralSpinLinear_mul, mul_inv_cancel,
          integralSpinLinear_one]
      inv_val := by
        rw [← integralSpinLinear_mul, inv_mul_cancel,
          integralSpinLinear_one] }
  map_one' := by
    apply Units.ext
    exact integralSpinLinear_one
  map_mul' g h := by
    apply Units.ext
    exact integralSpinLinear_mul g h

theorem integralSpinRepresentation_apply
    (g : integralSpin44) (X : IntegralZorn) :
    (integralSpinRepresentation g : Module.End ℤ IntegralZorn) X =
      integralSpinAction g X := rfl

/-- Scalar extension from the integral representation to the real split
carrier commutes with the real spin-vector action. -/
theorem integralSpinRepresentation_real_intertwining
    (g : integralSpin44) (X : IntegralZorn) :
    integralZornToRealSplit44
        ((integralSpinRepresentation g : Module.End ℤ IntegralZorn) X) =
      realSpinVectorLinear g.1 (integralZornToRealSplit44 X) := by
  rw [integralSpinRepresentation_apply, integralSpinAction_spec]

theorem integralSpinRepresentation_preserves_norm
    (g : integralSpin44) (X : IntegralZorn) :
    integralZornNorm
        ((integralSpinRepresentation g : Module.End ℤ IntegralZorn) X) =
      integralZornNorm X := by
  rw [integralSpinRepresentation_apply]
  exact integralSpinAction_preserves_norm g X

/-- Bundled arithmetic representation capstone. -/
theorem integral_spin_representation_triality_projective_closure
    (g : integralSpin44) (X Y : IntegralZorn)
    (S : CanonicalZornCompositionTriality.SpinorPlus8)
    (C : CanonicalZornCompositionTriality.SpinorMinus8) :
    integralZornToRealSplit44
        ((integralSpinRepresentation g : Module.End ℤ IntegralZorn) X) =
      realSpinVectorLinear g.1 (integralZornToRealSplit44 X) ∧
    integralZornNorm
        ((integralSpinRepresentation g : Module.End ℤ IntegralZorn) X) =
      integralZornNorm X ∧
    ProjectiveAffineConformalClosure55.Q55
      (ProjectiveAffineConformalClosure55.conformalEmbed44to55
        (realSplit44ToPAC44
          (realSpinVectorLinear g.1
            (integralZornToRealSplit44 X)))) = 0 := by
  exact ⟨integralSpinRepresentation_real_intertwining g X,
    integralSpinRepresentation_preserves_norm g X,
    (integralSpin44_arithmetic_triality_projective_closure
      g X Y S C).2.2.2.2.2.2.2.2⟩

end CanonicalZornIntegralSpinRepresentation

end noncomputable section
