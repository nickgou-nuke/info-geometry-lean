import InfoGeometry.Canonical.FilteredStarAlgebraFiniteGroupActionDirectLimit
import InfoGeometry.Canonical.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit
import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

/-!
# D₄-star observable direct-limit action

This file packages the honest stagewise color-permutation symmetry on the
observable algebra `D4StarObservable` as a compatible action on a constant
filtered star-inductive system, then descends it through the native filtered
star direct limit.

It does not claim a crossed-product completion or any noncommutative
structure on the observable carrier itself.
-/

noncomputable section

namespace InfoGeometry.Canonical.D4StarObservableDirectLimitAction

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit
open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

abbrev ObservableStage : ℕ → Type :=
  fun _ => D4StarObservable

/-- The constant filtered star-inductive system on the D₄ observable algebra. -/
def constantObservableSystem :
    ContinuousStarInductiveSystem ObservableStage where
  map := fun {_ _} _ => StarAlgHom.id ℂ D4StarObservable
  map_id := by
    intro n
    rfl
  map_comp := by
    intro m n k hmn hnk
    rfl

/-- The color permutation action as a star-algebra equivalence on the
observable algebra. -/
def colorPullbackStarRingEquiv
    (σ : Equiv.Perm ColorChannel) :
    D4StarObservable ≃⋆+* D4StarObservable where
  toRingEquiv := colorPullback σ
  map_star' := by
    intro f
    funext v
    rfl

/-- The same action, packaged as a star algebra equivalence. -/
def colorPullbackStarAlgEquiv
    (σ : Equiv.Perm ColorChannel) :
    D4StarObservable ≃⋆ₐ[ℂ] D4StarObservable :=
  StarAlgEquiv.mk (colorPullbackStarRingEquiv σ) (by
    intro r f
    rfl)

/-- The compatible finite-stage triality action on the constant observable
system. -/
def observableAction :
    CompatibleStarGroupAction ℕ (Equiv.Perm ColorChannel)
      ObservableStage (constantObservableSystem) where
  action := fun _ σ => colorPullbackStarAlgEquiv σ
  action_one := by
    intro n
    ext f v
    simp [colorPullbackStarAlgEquiv, colorPullbackStarRingEquiv, colorPullback_one]
  action_mul := by
    intro n σ τ
    ext f v
    simp [colorPullbackStarAlgEquiv, colorPullbackStarRingEquiv,
      colorPullback_mul]
  action_transition := by
    intro i j hij σ f
    rfl

/-- The descended action on the native filtered star direct limit of the
constant D₄ observable system. -/
def observableColimitAction (g : Equiv.Perm ColorChannel) :
    FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
      ObservableStage (constantObservableSystem) →⋆ₐ[ℂ]
    FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
      ObservableStage (constantObservableSystem) :=
  algebraicColimitGroupAction
    (I := ℕ) (G := Equiv.Perm ColorChannel)
    (Stage := ObservableStage) (sys := constantObservableSystem)
    (A := observableAction) g

@[simp] theorem observableColimitAction_on_stage
    (g : Equiv.Perm ColorChannel) (n : ℕ) (f : D4StarObservable) :
    observableColimitAction g
        (algebraicStarDirectLimitOf ObservableStage
          (constantObservableSystem) n f) =
      algebraicStarDirectLimitOf ObservableStage
        (constantObservableSystem) n
        (colorPullbackStarAlgEquiv g f) := by
  simpa [observableColimitAction, observableAction] using
    algebraicColimitGroupAction_on_stage
      (I := ℕ) (G := Equiv.Perm ColorChannel)
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction) g n f

@[simp] theorem observableColimitAction_one :
    observableColimitAction (1 : Equiv.Perm ColorChannel) =
      StarAlgHom.id ℂ
        (FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
          ObservableStage (constantObservableSystem)) := by
  simpa [observableColimitAction, observableAction] using
    algebraicColimitGroupAction_one
      (I := ℕ) (G := Equiv.Perm ColorChannel)
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction)

theorem observableColimitAction_mul
    (g h : Equiv.Perm ColorChannel) :
    observableColimitAction (g * h) =
      (observableColimitAction g).comp (observableColimitAction h) := by
  simpa [observableColimitAction, observableAction] using
    algebraicColimitGroupAction_mul
      (I := ℕ) (G := Equiv.Perm ColorChannel)
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction) g h

/-- The descended observable action packaged as a star-algebra equivalence. -/
noncomputable def observableColimitActionEquiv
    (g : Equiv.Perm ColorChannel) :
  FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
      ObservableStage (constantObservableSystem) ≃⋆ₐ[ℂ]
    FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
      ObservableStage (constantObservableSystem) :=
  algebraicColimitGroupActionEquiv
    (I := ℕ) (G := Equiv.Perm ColorChannel)
    (Stage := ObservableStage) (sys := constantObservableSystem)
    (A := observableAction) g

@[simp] theorem observableColimitActionEquiv_apply
    (g : Equiv.Perm ColorChannel) (x) :
    observableColimitActionEquiv g x =
      observableColimitAction g x := by
  simpa [observableColimitActionEquiv, observableColimitAction] using
    algebraicColimitGroupActionEquiv_apply
      (I := ℕ) (G := Equiv.Perm ColorChannel)
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction) g x

@[simp] theorem observableColimitActionEquiv_one :
    observableColimitActionEquiv (1 : Equiv.Perm ColorChannel) =
      (StarAlgEquiv.refl :
        FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
          ObservableStage (constantObservableSystem) ≃⋆ₐ[ℂ]
          FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit
            ObservableStage (constantObservableSystem)) := by
  simpa [observableColimitActionEquiv] using
    algebraicColimitGroupActionEquiv_one
      (I := ℕ) (G := Equiv.Perm ColorChannel)
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction)

theorem observableColimitActionEquiv_mul
    (g h : Equiv.Perm ColorChannel) :
    observableColimitActionEquiv (g * h) =
      (observableColimitActionEquiv h).trans
        (observableColimitActionEquiv g) := by
  simpa [observableColimitActionEquiv] using
    algebraicColimitGroupActionEquiv_mul
      (I := ℕ) (G := Equiv.Perm ColorChannel)
      (Stage := ObservableStage) (sys := constantObservableSystem)
      (A := observableAction) g h

end InfoGeometry.Canonical.D4StarObservableDirectLimitAction
