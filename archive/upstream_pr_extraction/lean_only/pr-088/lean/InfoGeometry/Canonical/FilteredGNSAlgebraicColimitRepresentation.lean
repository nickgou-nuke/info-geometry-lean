import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimit

/-!
# Representation of the algebraic star-colimit on the global GNS Hilbert space

The global stage representations form a compatible star-algebra cocone.
The universal property of the concrete filtered star direct limit therefore
produces one canonical `StarAlgHom` into the bounded operators on the global
filtered GNS Hilbert colimit.

This closes the algebraic representation descent.  Norm completion of the
source algebra is a separate subsequent construction.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalRepresentationCompatibility
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- Canonical representation of the concrete algebraic star direct limit on
the single global filtered GNS Hilbert colimit. -/
def algebraicColimitGNSRepresentation :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) :=
  liftStarAlgHom Stage sys
    (fun i =>
      globalStageRepresentationStarAlgHom
        Stage sys ω i)
    (fun hij x =>
      congrArg
        (fun T :
          GNSHilbertColimit Stage sys ω →L[ℂ]
            GNSHilbertColimit Stage sys ω =>
          T)
        (globalStageRepresentation_transition
          Stage sys ω hij x))

/-- The descended representation agrees strictly with each stage
representation on the corresponding canonical injection. -/
@[simp] theorem algebraicColimitGNSRepresentation_of
    (i : I) (a : Stage i) :
    algebraicColimitGNSRepresentation Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a) =
      globalStageRepresentationStarAlgHom
        Stage sys ω i a := by
  exact liftStarAlgHom_of
    Stage sys
    (fun i =>
      globalStageRepresentationStarAlgHom
        Stage sys ω i)
    (fun hij x =>
      globalStageRepresentation_transition
        Stage sys ω hij x)
    i a

/-- The colimit representation retains the finite-stage GNS action formula
on every later GNS stage image. -/
@[simp] theorem algebraicColimitGNSRepresentation_stage
    {i : I} (a : Stage i)
    (j : CStarStateColimit.Native.FilteredGNSTailRepresentation.UpperIndex i)
    (x : (ω.state j.1).functional.GNS) :
    algebraicColimitGNSRepresentation Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a)
        (gnsStageToHilbertColimit Stage sys ω j.1 x) =
      gnsStageToHilbertColimit Stage sys ω j.1
        (CStarStateColimit.Native.FilteredGNSTailRepresentation.tailGNSOperator
          Stage sys ω a j x) := by
  rw [algebraicColimitGNSRepresentation_of]
  exact globalStageRepresentation_stage
    Stage sys ω a j x

/-- The global GNS representation is the unique star-algebra map whose
restriction to every stage is the verified global stage representation. -/
theorem algebraicColimitGNSRepresentation_unique
    (F :
      AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
        (GNSHilbertColimit Stage sys ω →L[ℂ]
          GNSHilbertColimit Stage sys ω))
    (hF :
      ∀ i,
        F.comp (algebraicStarDirectLimitOf Stage sys i) =
          globalStageRepresentationStarAlgHom
            Stage sys ω i) :
    F = algebraicColimitGNSRepresentation Stage sys ω := by
  apply liftStarAlgHom_unique
    Stage sys
    (fun i =>
      globalStageRepresentationStarAlgHom
        Stage sys ω i)
    (fun hij x =>
      globalStageRepresentation_transition
        Stage sys ω hij x)
    F hF

end CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
