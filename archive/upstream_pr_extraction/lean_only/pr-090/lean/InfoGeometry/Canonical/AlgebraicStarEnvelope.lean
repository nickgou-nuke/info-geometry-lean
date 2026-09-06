import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimit

/-!
# Algebraic replacement for a C⋆ completion

In the finite/colimit framework the completion object is the concrete
filtered direct limit of star-algebras.  It carries multiplication and star
algebra structure and satisfies the genuine stagewise universal property.
No norm, metric completion, or C⋆-algebra instance is introduced here.
-/

noncomputable section
namespace InfoGeometry.Canonical.AlgebraicStarEnvelope

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit

universe u v

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

/-- The algebraic envelope carrier: a filtered star-algebra direct limit. -/
abbrev Carrier : Type u :=
  AlgebraicStarDirectLimit Stage sys

/-- Canonical injection of a finite stage into the algebraic envelope. -/
def stageInjection (i : I) : Stage i →⋆ₐ[ℂ] Carrier Stage sys :=
  algebraicStarDirectLimitOf Stage sys i

@[simp] theorem stageInjection_apply (i : I) (x : Stage i) :
    stageInjection Stage sys i x =
      algebraicStarDirectLimitOf Stage sys i x := rfl

theorem stageInjection_transition {i j : I} (hij : i ≤ j) (x : Stage i) :
    stageInjection Stage sys j (sys.map hij x) =
      stageInjection Stage sys i x := by
  exact algebraicStarDirectLimitOf_transition Stage sys hij x

/-- Compatible stage maps descend to a star-algebra map out of the envelope. -/
def lift {B : Type v} [Semiring B] [Algebra ℂ B] [Star B]
    (g : ∀ i, Stage i →⋆ₐ[ℂ] B)
    (hg : ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
      g j (sys.map hij x) = g i x) :
    Carrier Stage sys →⋆ₐ[ℂ] B :=
  liftStarAlgHom Stage sys g hg

@[simp] theorem lift_stage {B : Type v} [Semiring B] [Algebra ℂ B] [Star B]
    (g : ∀ i, Stage i →⋆ₐ[ℂ] B)
    (hg : ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
      g j (sys.map hij x) = g i x)
    (i : I) (x : Stage i) :
    lift Stage sys g hg (stageInjection Stage sys i x) = g i x := by
  exact liftStarAlgHom_of Stage sys g hg i x

theorem lift_unique {B : Type v} [Semiring B] [Algebra ℂ B] [Star B]
    (g : ∀ i, Stage i →⋆ₐ[ℂ] B)
    (hg : ∀ {i j : I} (hij : i ≤ j) (x : Stage i),
      g j (sys.map hij x) = g i x)
    (F : Carrier Stage sys →⋆ₐ[ℂ] B)
    (hF : ∀ i, F.comp (stageInjection Stage sys i) = g i) :
    F = lift Stage sys g hg := by
  apply liftStarAlgHom_unique Stage sys g hg F
  exact hF

end InfoGeometry.Canonical.AlgebraicStarEnvelope
end noncomputable section
