import InfoGeometry.Canonical.FilteredGNSRepresentedCStarCompletion
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transporting modular/KMS automorphisms to the represented completion

This owner adds the remaining theorem-honest layer:

* given a concrete automorphism of the represented operator closure,
  transport it to the completed represented carrier via
  `representedRangeCompletionStarAlgEquiv`;
* if the concrete automorphism is isometric, the transported map is
  isometric as well.

No analytic continuation is used.  Everything is transported through verified
star-algebra equivalences and native isometries.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCompletionModularTransport

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion

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

local instance globalBoundedOperatorCStarAlgebra :
    CStarAlgebra
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) where

/-- Transport a concrete represented-closure star-algebra automorphism to the
completed represented carrier. -/
def transportStarAlgAutFromClosure
    (σ : representedCStarClosure Stage sys ω ≃⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω) :
    representedAlgebraicRangeCompletion Stage sys ω ≃⋆ₐ[ℂ]
      representedAlgebraicRangeCompletion Stage sys ω :=
  (representedRangeCompletionStarAlgEquiv Stage sys ω).trans
    (σ.trans (representedRangeCompletionStarAlgEquiv Stage sys ω).symm)

@[simp] theorem transportStarAlgAutFromClosure_apply
    (σ : representedCStarClosure Stage sys ω ≃⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω)
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    transportStarAlgAutFromClosure Stage sys ω σ x =
      (representedRangeCompletionStarAlgEquiv Stage sys ω).symm
        (σ ((representedRangeCompletionStarAlgEquiv Stage sys ω) x)) :=
  rfl

/-- If the concrete represented-closure automorphism is isometric, then its
transport to the completed represented carrier is isometric. -/
theorem transportStarAlgAutFromClosure_isometry
    (σ : representedCStarClosure Stage sys ω ≃⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω)
    (hσ : Isometry (σ : representedCStarClosure Stage sys ω →
      representedCStarClosure Stage sys ω)) :
    Isometry
      (transportStarAlgAutFromClosure Stage sys ω σ :
        representedAlgebraicRangeCompletion Stage sys ω →
          representedAlgebraicRangeCompletion Stage sys ω) := by
  let e := representedRangeCompletionEquiv Stage sys ω
  have hcomp :
      Isometry
        ((e.symm : representedCStarClosure Stage sys ω →
          representedAlgebraicRangeCompletion Stage sys ω) ∘
          ((σ : representedCStarClosure Stage sys ω →
            representedCStarClosure Stage sys ω) ∘
            (e : representedAlgebraicRangeCompletion Stage sys ω →
              representedCStarClosure Stage sys ω))) :=
    e.symm.isometry.comp (hσ.comp e.isometry)
  simpa [transportStarAlgAutFromClosure, e]
    using hcomp

/-- A packaged modular/KMS candidate on the completed represented carrier:
a transported star-automorphism together with its isometry proof. -/
structure TransportedStarIsometricAutomorphism where
  aut : representedAlgebraicRangeCompletion Stage sys ω ≃⋆ₐ[ℂ]
    representedAlgebraicRangeCompletion Stage sys ω
  isometric : Isometry (aut : representedAlgebraicRangeCompletion Stage sys ω →
    representedAlgebraicRangeCompletion Stage sys ω)

/-- Build a completed-carrier star-isometric automorphism from a concrete
represented-closure one plus an explicit isometry hypothesis. -/
def mkTransportedStarIsometricAutomorphism
    (σ : representedCStarClosure Stage sys ω ≃⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω)
    (hσ : Isometry (σ : representedCStarClosure Stage sys ω →
      representedCStarClosure Stage sys ω)) :
    TransportedStarIsometricAutomorphism Stage sys ω where
  aut := transportStarAlgAutFromClosure Stage sys ω σ
  isometric := transportStarAlgAutFromClosure_isometry Stage sys ω σ hσ

end CStarStateColimit.Native.FilteredGNSRepresentedCompletionModularTransport
