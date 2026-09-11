import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compatible noncommutative actions on the native filtered star direct limit

This owner descends a stagewise `ℤ`-indexed family of star-algebra maps through
the existing concrete `DirectLimit` carrier.  It deliberately does not use a
`TopCat` colimit and does not assert a crossed-product colimit theorem.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraActionDirectLimit

open CStarStateColimit.Native
open FilteredStarAlgebraDirectLimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

structure CompatibleStarAction where
  action : ∀ i, ℤ → Stage i →⋆ₐ[ℂ] Stage i
  action_zero : ∀ i, action i 0 = StarAlgHom.id ℂ (Stage i)
  action_add : ∀ i (s t : ℤ),
    action i (s + t) = (action i t).comp (action i s)
  action_transition : ∀ {i j : I} (hij : i ≤ j) (t : ℤ) (x : Stage i),
    sys.map hij (action i t x) = action j t (sys.map hij x)

variable (A : CompatibleStarAction Stage sys)

def actionFamily (t : ℤ) (i : I) :
    Stage i →⋆ₐ[ℂ]
      FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys :=
  (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i).comp
    (A.action i t)

theorem actionFamily_compatible (t : ℤ) {i j : I} (hij : i ≤ j) (x : Stage i) :
    actionFamily Stage sys A t j (sys.map hij x) =
      actionFamily Stage sys A t i x := by
  change
    FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys j
        (A.action j t (sys.map hij x)) =
      FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i
        (A.action i t x)
  rw [← A.action_transition hij t x]
  exact
    FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf_transition
      Stage sys hij (A.action i t x)

noncomputable def algebraicColimitAction (t : ℤ) :
    FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys :=
  FilteredStarAlgebraDirectLimit.liftStarAlgHom Stage sys
    (actionFamily Stage sys A t)
    (actionFamily_compatible Stage sys A t)

@[simp] theorem algebraicColimitAction_on_stage
    (t : ℤ) (i : I) (x : Stage i) :
    algebraicColimitAction Stage sys A t
        (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i x) =
      FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i
        (A.action i t x) := by
  exact FilteredStarAlgebraDirectLimit.liftStarAlgHom_of
    Stage sys (actionFamily Stage sys A t)
    (actionFamily_compatible Stage sys A t) i x

theorem algebraicColimitAction_transition_natural
    (t : ℤ) {i j : I} (hij : i ≤ j) (x : Stage i) :
    algebraicColimitAction Stage sys A t
        (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys j
          (sys.map hij x)) =
      algebraicColimitAction Stage sys A t
        (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i x) := by
  rw [algebraicColimitAction_on_stage, algebraicColimitAction_on_stage]
  rw [← A.action_transition hij t x]
  exact FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf_transition
    Stage sys hij (A.action i t x)

theorem algebraicColimitAction_zero :
    algebraicColimitAction Stage sys A 0 =
      StarAlgHom.id ℂ
        (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  have huniq :
      StarAlgHom.id ℂ
          (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) =
        algebraicColimitAction Stage sys A 0 := by
    apply FilteredStarAlgebraDirectLimit.liftStarAlgHom_unique
      Stage sys (actionFamily Stage sys A 0)
      (actionFamily_compatible Stage sys A 0)
      (StarAlgHom.id ℂ _)
    intro i
    ext x
    simp [actionFamily, A.action_zero]
  exact huniq.symm

theorem algebraicColimitAction_add (s t : ℤ) :
    algebraicColimitAction Stage sys A (s + t) =
      (algebraicColimitAction Stage sys A t).comp
        (algebraicColimitAction Stage sys A s) := by
  have huniq :
      (algebraicColimitAction Stage sys A t).comp
          (algebraicColimitAction Stage sys A s) =
        algebraicColimitAction Stage sys A (s + t) := by
    apply FilteredStarAlgebraDirectLimit.liftStarAlgHom_unique
      Stage sys (actionFamily Stage sys A (s + t))
      (actionFamily_compatible Stage sys A (s + t))
      ((algebraicColimitAction Stage sys A t).comp
        (algebraicColimitAction Stage sys A s))
    intro i
    ext x
    simp only [StarAlgHom.comp_apply, algebraicColimitAction_on_stage]
    change
      FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i
          (A.action i t (A.action i s x)) =
        FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i
          (A.action i (s + t) x)
    rw [A.action_add]
    rfl
  exact huniq.symm

theorem algebraicColimitAction_comp_neg
    (t : ℤ) :
    (algebraicColimitAction Stage sys A (-t)).comp
        (algebraicColimitAction Stage sys A t) =
      StarAlgHom.id ℂ
        (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  calc
    (algebraicColimitAction Stage sys A (-t)).comp
        (algebraicColimitAction Stage sys A t) =
      algebraicColimitAction Stage sys A (t + (-t)) := by
        symm
        exact algebraicColimitAction_add Stage sys A t (-t)
    _ = algebraicColimitAction Stage sys A 0 := by
      rw [add_neg_cancel]
    _ = StarAlgHom.id ℂ
        (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) :=
      algebraicColimitAction_zero Stage sys A

theorem algebraicColimitAction_neg_comp
    (t : ℤ) :
    (algebraicColimitAction Stage sys A t).comp
        (algebraicColimitAction Stage sys A (-t)) =
      StarAlgHom.id ℂ
        (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  calc
    (algebraicColimitAction Stage sys A t).comp
        (algebraicColimitAction Stage sys A (-t)) =
      algebraicColimitAction Stage sys A ((-t) + t) := by
        symm
        exact algebraicColimitAction_add Stage sys A (-t) t
    _ = algebraicColimitAction Stage sys A 0 := by
      rw [neg_add_cancel]
    _ = StarAlgHom.id ℂ
        (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) :=
      algebraicColimitAction_zero Stage sys A


end CStarStateColimit.Native.FilteredStarAlgebraActionDirectLimit
