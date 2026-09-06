import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimit

/-!
# Finite-group actions on the native filtered star-algebra direct limit

The carrier is Mathlib's concrete noncommutative `DirectLimit`.  This owner
descends a compatible family of stagewise `StarAlgEquiv`s and proves the
group laws of the induced star-algebra maps.  It does not assert a crossed-
product colimit or a C*-completion.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit

open CStarStateColimit.Native
open FilteredStarAlgebraDirectLimit

universe u

structure CompatibleStarGroupAction
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage) where
  action : ∀ i, G → Stage i ≃⋆ₐ[ℂ] Stage i
  action_one : ∀ i, action i 1 =
    (StarAlgEquiv.refl : Stage i ≃⋆ₐ[ℂ] Stage i)
  action_mul : ∀ i (g h : G),
    action i (g * h) = (action i h).trans (action i g)
  action_transition : ∀ {i j : I} (hij : i ≤ j) (g : G) (x : Stage i),
    sys.map hij (action i g x) = action j g (sys.map hij x)

def actionFamily
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g : G) (i : I) :
    Stage i →⋆ₐ[ℂ] AlgebraicStarDirectLimit Stage sys :=
  (algebraicStarDirectLimitOf Stage sys i).comp
    (A.action i g : Stage i →⋆ₐ[ℂ] Stage i)

theorem actionFamily_compatible
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g : G)
    {i j : I} (hij : i ≤ j) (x : Stage i) :
    actionFamily I G Stage sys A g j (sys.map hij x) =
      actionFamily I G Stage sys A g i x := by
  change algebraicStarDirectLimitOf Stage sys j
      (A.action j g (sys.map hij x)) =
    algebraicStarDirectLimitOf Stage sys i (A.action i g x)
  rw [← A.action_transition hij g x]
  exact algebraicStarDirectLimitOf_transition Stage sys hij (A.action i g x)

noncomputable def algebraicColimitGroupAction
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g : G) :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      AlgebraicStarDirectLimit Stage sys :=
  liftStarAlgHom Stage sys
    (actionFamily I G Stage sys A g)
    (actionFamily_compatible I G Stage sys A g)

@[simp] theorem algebraicColimitGroupAction_on_stage
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g : G) (i : I) (x : Stage i) :
    algebraicColimitGroupAction I G Stage sys A g
        (algebraicStarDirectLimitOf Stage sys i x) =
      algebraicStarDirectLimitOf Stage sys i (A.action i g x) := by
  exact liftStarAlgHom_of Stage sys
    (actionFamily I G Stage sys A g)
    (actionFamily_compatible I G Stage sys A g) i x

theorem algebraicColimitGroupAction_one
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) :
    algebraicColimitGroupAction I G Stage sys A 1 =
      StarAlgHom.id ℂ (AlgebraicStarDirectLimit Stage sys) := by
  have huniq := (liftStarAlgHom_unique Stage sys
    (actionFamily I G Stage sys A 1)
    (actionFamily_compatible I G Stage sys A 1)
    (StarAlgHom.id ℂ _)) (by
    intro i
    ext x
    simp [actionFamily, A.action_one])
  exact huniq.symm

theorem algebraicColimitGroupAction_mul
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g h : G) :
    algebraicColimitGroupAction I G Stage sys A (g * h) =
      (algebraicColimitGroupAction I G Stage sys A g).comp
        (algebraicColimitGroupAction I G Stage sys A h) := by
  have huniq := (liftStarAlgHom_unique Stage sys
    (actionFamily I G Stage sys A (g * h))
    (actionFamily_compatible I G Stage sys A (g * h))
    ((algebraicColimitGroupAction I G Stage sys A g).comp
      (algebraicColimitGroupAction I G Stage sys A h))) (by
    intro i
    ext x
    simp only [StarAlgHom.comp_apply,
      algebraicColimitGroupAction_on_stage]
    change algebraicStarDirectLimitOf Stage sys i
        (A.action i g (A.action i h x)) =
      algebraicStarDirectLimitOf Stage sys i (A.action i (g * h) x)
    rw [A.action_mul]
    rfl)
  exact huniq.symm

theorem algebraicColimitGroupAction_inv_comp
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g : G) :
    (algebraicColimitGroupAction I G Stage sys A g⁻¹).comp
        (algebraicColimitGroupAction I G Stage sys A g) =
      StarAlgHom.id ℂ (AlgebraicStarDirectLimit Stage sys) := by
  rw [← algebraicColimitGroupAction_mul I G Stage sys A g⁻¹ g]
  simpa using algebraicColimitGroupAction_one I G Stage sys A

theorem algebraicColimitGroupAction_comp_inv
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (g : G) :
    (algebraicColimitGroupAction I G Stage sys A g).comp
        (algebraicColimitGroupAction I G Stage sys A g⁻¹) =
      StarAlgHom.id ℂ (AlgebraicStarDirectLimit Stage sys) := by
  rw [← algebraicColimitGroupAction_mul I G Stage sys A g g⁻¹]
  simpa using algebraicColimitGroupAction_one I G Stage sys A

end CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
