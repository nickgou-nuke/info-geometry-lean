import InfoGeometry.Canonical.FilteredGNSRepresentedCStarModularAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic KMS states on the completed represented carrier

This owner records the algebraic KMS boundary law for a previously supplied
star-automorphism flow.  It deliberately does not assert analytic continuation,
positivity, or existence of a state.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSCompletionKMSState

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedCStarModularAutomorphism

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

abbrev Carrier : Type _ :=
  representedAlgebraicRangeCompletion Stage sys ω

/-- A state together with an explicitly supplied algebraic modular flow and
its KMS boundary identity at inverse temperature `beta`. -/
structure Data where
  beta : ℝ
  state : Carrier Stage sys ω → ℂ
  flow : CompletionModularFlow Stage sys ω
  kms_boundary : ∀ A B : Carrier Stage sys ω,
    state (A * (flow.toAut beta) B) = state (B * A)

def IsKMS (d : Data Stage sys ω) : Prop :=
  ∀ A B : Carrier Stage sys ω,
    d.state (A * (d.flow.toAut d.beta) B) = d.state (B * A)

theorem isKMS (d : Data Stage sys ω) : IsKMS Stage sys ω d :=
  d.kms_boundary

theorem flow_zero (d : Data Stage sys ω) (A : Carrier Stage sys ω) :
    d.flow.toAut 0 A = A := by
  rw [d.flow.map_zero]
  rfl

theorem flow_add (d : Data Stage sys ω) (s t : ℝ)
    (A : Carrier Stage sys ω) :
    d.flow.toAut (s + t) A =
      d.flow.toAut t (d.flow.toAut s A) := by
  rw [d.flow.map_add]
  rfl

end CStarStateColimit.Native.FilteredGNSCompletionKMSState
