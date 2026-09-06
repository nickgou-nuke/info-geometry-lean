import Mathlib
import InfoGeometry.KK.RealSplitKreinResolvent

/-!
# Linear domain refinement of the primitive split-Krein resolvent packet

The primitive resolvent owner stores a set-valued domain and a function on its
subtype.  This owner adds only the next algebraic layer: the domain is a real
submodule and the operator is a linear map on that domain.  It proves the
domain-sensitive range statement for the resolvent when the shifted operator
is injective.

No density, closedness, self-adjointness, regularity, or Kasparov class is
claimed here.
-/

noncomputable section

namespace InfoGeometry.KK.RealSplitKreinLinearResolventBridge

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinResolventData

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

structure RealSplitKreinLinearResolventData
    (domain : Submodule ℝ H)
    (D : domain →ₗ[ℝ] H)
    extends RealSplitKreinResolventData H (domain : Set H) D where

def shifted
    {domain : Submodule ℝ H}
    {D : domain →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData domain D) :
    domain →ₗ[ℝ] H where
  toFun x := D x - R.shift • x.1
  map_add' x y := by
    simp [sub_eq_add_neg]
    abel
  map_smul' c x := by
    simp [smul_sub, smul_smul, mul_comm]

@[simp] theorem shifted_apply
    {domain : Submodule ℝ H}
    {D : domain →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData domain D)
    (x : domain) :
    shifted R x = D x - R.shift • x.1 := rfl

theorem shifted_apply_resolvent
    {domain : Submodule ℝ H}
    {D : domain →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData domain D)
    (x : H) :
    shifted R ⟨R.resolvent x, R.resolvent_preserves_domain x⟩ = x := by
  exact R.left_resolvent x

theorem shifted_surjective
    {domain : Submodule ℝ H}
    {D : domain →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData domain D) :
    Function.Surjective (shifted R) := by
  intro x
  exact ⟨⟨R.resolvent x, R.resolvent_preserves_domain x⟩,
    shifted_apply_resolvent R x⟩

theorem range_resolvent_eq_domain
    {domain : Submodule ℝ H}
    {D : domain →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData domain D)
    (hinj : Function.Injective (shifted R)) :
    LinearMap.range R.resolvent.toLinearMap = domain := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact R.resolvent_preserves_domain x
  · intro y hy
    refine ⟨shifted R ⟨y, hy⟩, ?_⟩
    have hsub :
        (⟨R.resolvent (shifted R ⟨y, hy⟩),
          R.resolvent_preserves_domain (shifted R ⟨y, hy⟩)⟩ : domain) =
          ⟨y, hy⟩ := by
      apply hinj
      exact shifted_apply_resolvent R (shifted R ⟨y, hy⟩)
    exact congrArg Subtype.val hsub

theorem resolvent_shifted_apply
    {domain : Submodule ℝ H}
    {D : domain →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData domain D)
    (hinj : Function.Injective (shifted R))
    (x : domain) :
    R.resolvent (shifted R x) = x.1 := by
  have hsub :
      (⟨R.resolvent (shifted R x),
        R.resolvent_preserves_domain (shifted R x)⟩ : domain) = x := by
    apply hinj
    exact shifted_apply_resolvent R (shifted R x)
  exact congrArg Subtype.val hsub

end InfoGeometry.KK.RealSplitKreinLinearResolventBridge
