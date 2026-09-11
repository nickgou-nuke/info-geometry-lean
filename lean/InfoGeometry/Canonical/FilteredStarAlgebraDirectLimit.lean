import InfoGeometry.Canonical.FilteredGNSGlobalRepresentationCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Concrete filtered direct limits of noncommutative star algebras

This file equips Mathlib's explicit directed `DirectLimit` quotient with the
complex algebra and involution inherited from a continuous star-inductive
system.  It then bundles the canonical stage injections and universal descent
as genuine `StarAlgHom`s.

This is an algebraic star-colimit.  No norm or C-star completion is asserted.
The construction remains noncommutative and retains concrete finite-stage
representatives.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraDirectLimit

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native

universe u v

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

/-- The bundled star-algebra transition used by Mathlib's concrete directed
limit. -/
def starTransition {i j : I} (hij : i ≤ j) :
    Stage i →⋆ₐ[ℂ] Stage j :=
  sys.map hij

/-- The transition maps of a continuous star-inductive system form a
Mathlib `DirectedSystem`. -/
instance starTransitionDirectedSystem :
    DirectedSystem Stage
      (fun _ _ hij => starTransition Stage sys hij) where
  map_self := by
    intro i x
    unfold starTransition
    rw [sys.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    unfold starTransition
    rw [← sys.map_comp hij hjk]
    rfl

/-- Concrete algebraic carrier of the filtered star-algebra direct limit. -/
abbrev AlgebraicStarDirectLimit : Type u :=
  DirectLimit Stage
    (fun _ _ hij => starTransition Stage sys hij)

/-- The complex module structure inherited by `DirectLimit` is compatible
with its noncommutative multiplication. -/
instance algebraicStarDirectLimitAlgebra :
    Algebra ℂ (AlgebraicStarDirectLimit Stage sys) :=
  Algebra.ofModule
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ i x y =>
          simp [DirectLimit.smul_def, DirectLimit.mul_def])
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ i x y =>
          simp [DirectLimit.smul_def, DirectLimit.mul_def])

/-- Stagewise involution descends through the filtered quotient because all
transition maps preserve star. -/
instance algebraicStarDirectLimitStar :
    Star (AlgebraicStarDirectLimit Stage sys) where
  star :=
    DirectLimit.map
      (fun _ _ hij => starTransition Stage sys hij)
      (fun _ _ hij => starTransition Stage sys hij)
      (fun _ x => star x)
      (by
        intro i j hij x
        exact map_star (sys.map hij) x)

@[simp] theorem star_mk
    (i : I) (x : Stage i) :
    star
        (⟦⟨i, x⟩⟧ :
          AlgebraicStarDirectLimit Stage sys) =
      (⟦⟨i, star x⟩⟧ :
        AlgebraicStarDirectLimit Stage sys) :=
  rfl

/-- The descended involution satisfies the noncommutative star-ring laws. -/
instance algebraicStarDirectLimitStarRing :
    StarRing (AlgebraicStarDirectLimit Stage sys) where
  star_involutive := by
    intro x
    induction x using DirectLimit.induction with
    | _ i x => simp
  star_add := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
        rw [DirectLimit.add_def, star_mk, star_mk,
          star_mk, DirectLimit.add_def, star_add]
  star_mul := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
        rw [DirectLimit.mul_def, star_mk, star_mk,
          star_mk, DirectLimit.mul_def, star_mul]

/-- Canonical star-algebra injection of one finite stage into the concrete
algebraic direct limit. -/
def algebraicStarDirectLimitOf
    (i : I) :
    Stage i →⋆ₐ[ℂ]
      AlgebraicStarDirectLimit Stage sys where
  toFun :=
    DirectLimit.Ring.of Stage
      (fun _ _ hij => starTransition Stage sys hij) i
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    change
      (⟦⟨i, c • 1⟩⟧ :
          AlgebraicStarDirectLimit Stage sys) =
        c • (1 : AlgebraicStarDirectLimit Stage sys)
    rw [DirectLimit.one_def i, DirectLimit.smul_def]
  map_star' := by
    intro x
    rfl

@[simp] theorem algebraicStarDirectLimitOf_apply
    (i : I) (x : Stage i) :
    algebraicStarDirectLimitOf Stage sys i x =
      (⟦⟨i, x⟩⟧ :
        AlgebraicStarDirectLimit Stage sys) :=
  rfl

/-- Canonical injections identify every element with all of its later
transition representatives. -/
theorem algebraicStarDirectLimitOf_transition
    {i j : I} (hij : i ≤ j) (x : Stage i) :
    algebraicStarDirectLimitOf Stage sys j
        (sys.map hij x) =
      algebraicStarDirectLimitOf Stage sys i x := by
  exact
    DirectLimit.Ring.of_f
      (G := Stage)
      (f := fun _ _ hij => starTransition Stage sys hij)
      hij x

variable {B : Type v}
variable [Semiring B] [Algebra ℂ B] [Star B]

/-- Universal star-algebra descent from a compatible family of stage
representations. -/
def liftStarAlgHom
    (g : ∀ i, Stage i →⋆ₐ[ℂ] B)
    (hg :
      ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
        g j (sys.map hij x) = g i x) :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B where
  toFun :=
    DirectLimit.Ring.lift
      Stage
      (fun _ _ hij => starTransition Stage sys hij)
      B
      (fun i => (g i).toAlgHom.toRingHom)
      (fun i j hij x => hg hij x)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := by
    intro c
    let i : I := Classical.choice inferInstance
    rw [← (algebraicStarDirectLimitOf Stage sys i).commutes c]
    change
      DirectLimit.Ring.lift
          Stage
          (fun _ _ hij => starTransition Stage sys hij)
          B
          (fun i => (g i).toAlgHom.toRingHom)
          (fun i j hij x => hg hij x)
          (DirectLimit.Ring.of
            Stage
            (fun _ _ hij => starTransition Stage sys hij)
            i ((algebraMap ℂ (Stage i)) c)) =
        (algebraMap ℂ B) c
    rw [DirectLimit.Ring.lift_of]
    exact (g i).commutes c
  map_star' := by
    intro z
    induction z using DirectLimit.induction with
    | _ i x =>
        rw [star_mk]
        change g i (star x) = star (g i x)
        exact map_star (g i) x

@[simp] theorem liftStarAlgHom_of
    (g : ∀ i, Stage i →⋆ₐ[ℂ] B)
    (hg :
      ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
        g j (sys.map hij x) = g i x)
    (i : I) (x : Stage i) :
    liftStarAlgHom Stage sys g hg
        (algebraicStarDirectLimitOf Stage sys i x) =
      g i x := by
  rfl

/-- A star-algebra map out of the concrete direct limit is uniquely
determined by its values on all stage injections. -/
theorem liftStarAlgHom_unique
    (g : ∀ i, Stage i →⋆ₐ[ℂ] B)
    (hg :
      ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
        g j (sys.map hij x) = g i x)
    (F : AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] B)
    (hF :
      ∀ i,
        F.comp (algebraicStarDirectLimitOf Stage sys i) =
          g i) :
    F = liftStarAlgHom Stage sys g hg := by
  ext z
  induction z using DirectLimit.induction with
  | _ i x =>
      have hi := congrArg
        (fun f : Stage i →⋆ₐ[ℂ] B => f x)
        (hF i)
      simpa using hi

end CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
