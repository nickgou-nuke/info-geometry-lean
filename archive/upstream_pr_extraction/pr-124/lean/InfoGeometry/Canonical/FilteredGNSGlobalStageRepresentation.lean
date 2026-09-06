import InfoGeometry.Canonical.FilteredGNSCofinalTail

/-!
# Global stage representations transported from cofinal GNS tails

For an observable belonging to one stage, its completed representation is
first constructed on the cofinal upper-tail GNS Hilbert colimit.  The
canonical unitary equivalence from that tail completion to the global
filtered GNS Hilbert colimit then transports the representation by unitary
conjugation.

Mathlib's `LinearIsometryEquiv.conjStarAlgEquiv` performs this transport as a
star-algebra equivalence of bounded-operator algebras.  Thus multiplication,
the unit, complex scalars, and the Hilbert adjoint are preserved by the
bundled construction itself.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
open CStarStateColimit.Native.FilteredGNSCofinalTail
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

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

local notation "E" =>
  TailGNSStage Stage sys ω
local notation "S" =>
  tailGNSIsometricDirectSystem Stage sys ω

/-- A stage algebra acts on the single global filtered GNS Hilbert colimit
by conjugating its cofinal-tail representation through the canonical
tail-to-global unitary equivalence. -/
def globalStageRepresentationStarAlgHom
    (i₀ : I) :
    Stage i₀ →⋆ₐ[ℂ]
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) :=
  ((tailHilbertGlobalEquiv Stage sys ω i₀).conjStarAlgEquiv :
      (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
          HilbertDirectLimit (E i₀) (S i₀)) →⋆ₐ[ℂ]
        (GNSHilbertColimit Stage sys ω →L[ℂ]
          GNSHilbertColimit Stage sys ω)).comp
    (tailCompletedRepresentationStarAlgHom
      Stage sys ω i₀)

@[simp] theorem globalStageRepresentation_apply
    {i₀ : I} (a : Stage i₀)
    (z : GNSHilbertColimit Stage sys ω) :
    globalStageRepresentationStarAlgHom Stage sys ω i₀ a z =
      tailHilbertGlobalEquiv Stage sys ω i₀
        (tailCompletedRepresentation Stage sys ω a
          ((tailHilbertGlobalEquiv Stage sys ω i₀).symm z)) :=
  rfl

/-- The canonical cofinal unitary strictly intertwines the tail
representation with its transported global representation. -/
theorem globalStageRepresentation_intertwines
    {i₀ : I} (a : Stage i₀) :
    (globalStageRepresentationStarAlgHom
        Stage sys ω i₀ a).comp
      (tailHilbertGlobalEquiv
        Stage sys ω i₀).toContinuousLinearEquiv.toContinuousLinearMap =
      (tailHilbertGlobalEquiv
        Stage sys ω i₀).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (tailCompletedRepresentation Stage sys ω a) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [globalStageRepresentation_apply]
  change
    tailHilbertGlobalEquiv Stage sys ω i₀
        (tailCompletedRepresentation Stage sys ω a
          ((tailHilbertGlobalEquiv Stage sys ω i₀).symm
            (tailHilbertGlobalEquiv Stage sys ω i₀ z))) =
      tailHilbertGlobalEquiv Stage sys ω i₀
        (tailCompletedRepresentation Stage sys ω a z)
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- On every upper-tail stage image, the transported global representation
is exactly the native GNS left action of the transported observable. -/
@[simp] theorem globalStageRepresentation_stage
    {i₀ : I} (a : Stage i₀)
    (j : UpperIndex i₀) (x : E i₀ j) :
    globalStageRepresentationStarAlgHom Stage sys ω i₀ a
        (gnsStageToHilbertColimit Stage sys ω j.1 x) =
      gnsStageToHilbertColimit Stage sys ω j.1
        (tailGNSOperator Stage sys ω a j x) := by
  calc
    globalStageRepresentationStarAlgHom Stage sys ω i₀ a
          (gnsStageToHilbertColimit Stage sys ω j.1 x) =
        tailHilbertGlobalEquiv Stage sys ω i₀
          (tailCompletedRepresentation Stage sys ω a
            ((tailHilbertGlobalEquiv Stage sys ω i₀).symm
              (tailHilbertGlobalEquiv Stage sys ω i₀
                (stageToHilbertDirectLimit (E i₀) (S i₀) j x)))) := by
          rw [tailHilbertGlobalEquiv_stage]
          rfl
    _ = tailHilbertGlobalEquiv Stage sys ω i₀
          (tailCompletedRepresentation Stage sys ω a
            (stageToHilbertDirectLimit (E i₀) (S i₀) j x)) := by
          rw [LinearIsometryEquiv.symm_apply_apply]
    _ = tailHilbertGlobalEquiv Stage sys ω i₀
          (stageToHilbertDirectLimit (E i₀) (S i₀) j
            (tailGNSOperator Stage sys ω a j x)) := by
          rw [tailCompletedRepresentation_stage]
    _ = gnsStageToHilbertColimit Stage sys ω j.1
          (tailGNSOperator Stage sys ω a j x) := by
          rw [tailHilbertGlobalEquiv_stage]

/-- Unitary transport preserves all matrix coefficients of the represented
stage observable. -/
theorem globalStageRepresentation_inner
    {i₀ : I} (a : Stage i₀)
    (x y : HilbertDirectLimit (E i₀) (S i₀)) :
    inner ℂ
        (tailHilbertGlobalEquiv Stage sys ω i₀ x)
        (globalStageRepresentationStarAlgHom
          Stage sys ω i₀ a
          (tailHilbertGlobalEquiv Stage sys ω i₀ y)) =
      inner ℂ x
        (tailCompletedRepresentation Stage sys ω a y) := by
  rw [globalStageRepresentation_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact
    (tailHilbertGlobalEquiv
      Stage sys ω i₀).inner_map_map x
        (tailCompletedRepresentation Stage sys ω a y)

end CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
