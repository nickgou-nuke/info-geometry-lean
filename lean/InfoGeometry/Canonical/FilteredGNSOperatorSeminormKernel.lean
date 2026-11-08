import InfoGeometry.Canonical.FilteredGNSRepresentedCStarClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Operator C-star seminorm and representation kernel

The global filtered GNS representation pulls the bounded-operator norm back
to a submultiplicative ring seminorm on the concrete algebraic star-colimit.
Its null space is exactly the kernel ideal of the representation.  The
seminorm is star-invariant and satisfies the C-star identity before any
quotient or completion is formed.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSOperatorSeminormKernel

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation

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

/-- Pullback of the bounded-operator norm along the algebraic colimit GNS
representation. -/
def representedOperatorRingSeminorm :
    RingSeminorm (AlgebraicStarDirectLimit Stage sys) where
  toFun := fun a =>
    ‖algebraicColimitGNSRepresentation Stage sys ω a‖
  map_zero' := by
    rw [map_zero]
    exact ContinuousLinearMap.opNorm_zero
  add_le' := by
    intro a b
    rw [map_add]
    exact ContinuousLinearMap.opNorm_add_le _ _
  neg' := by
    intro a
    rw [map_neg]
    exact ContinuousLinearMap.opNorm_neg _
  mul_le' := by
    intro a b
    rw [map_mul]
    exact ContinuousLinearMap.opNorm_comp_le _ _

@[simp] theorem representedOperatorRingSeminorm_apply
    (a : AlgebraicStarDirectLimit Stage sys) :
    representedOperatorRingSeminorm Stage sys ω a =
      ‖algebraicColimitGNSRepresentation
        Stage sys ω a‖ :=
  rfl

/-- The represented seminorm is invariant under the algebra involution. -/
theorem representedOperatorRingSeminorm_star
    (a : AlgebraicStarDirectLimit Stage sys) :
    representedOperatorRingSeminorm Stage sys ω (star a) =
      representedOperatorRingSeminorm Stage sys ω a := by
  rw [representedOperatorRingSeminorm_apply,
    representedOperatorRingSeminorm_apply,
    map_star]
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact
    (ContinuousLinearMap.adjoint).norm_map
      (algebraicColimitGNSRepresentation
        Stage sys ω a)

/-- The represented seminorm satisfies the exact C-star identity. -/
theorem representedOperatorRingSeminorm_cstar
    (a : AlgebraicStarDirectLimit Stage sys) :
    representedOperatorRingSeminorm Stage sys ω (star a * a) =
      representedOperatorRingSeminorm Stage sys ω a *
        representedOperatorRingSeminorm Stage sys ω a := by
  rw [representedOperatorRingSeminorm_apply,
    representedOperatorRingSeminorm_apply,
    map_mul, map_star]
  exact CStarRing.norm_star_mul_self
    (x := algebraicColimitGNSRepresentation
      Stage sys ω a)

/-- Kernel ideal of the global algebraic-colimit representation. -/
def representationKernel :
    Ideal (AlgebraicStarDirectLimit Stage sys) :=
  RingHom.ker
    (algebraicColimitGNSRepresentation
      Stage sys ω).toAlgHom.toRingHom

@[simp] theorem mem_representationKernel_iff
    (a : AlgebraicStarDirectLimit Stage sys) :
    a ∈ representationKernel Stage sys ω ↔
      algebraicColimitGNSRepresentation
        Stage sys ω a = 0 :=
  RingHom.mem_ker

/-- Vanishing of the represented operator seminorm is precisely membership
in the representation kernel. -/
theorem representedOperatorRingSeminorm_eq_zero_iff
    (a : AlgebraicStarDirectLimit Stage sys) :
    representedOperatorRingSeminorm Stage sys ω a = 0 ↔
      a ∈ representationKernel Stage sys ω := by
  rw [representedOperatorRingSeminorm_apply,
    mem_representationKernel_iff]
  exact ContinuousLinearMap.opNorm_zero_iff _

/-- The representation kernel is invariant under involution. -/
theorem star_mem_representationKernel_iff
    (a : AlgebraicStarDirectLimit Stage sys) :
    star a ∈ representationKernel Stage sys ω ↔
      a ∈ representationKernel Stage sys ω := by
  simp only [mem_representationKernel_iff, map_star, star_eq_zero]

theorem representationKernel_star_mem
    {a : AlgebraicStarDirectLimit Stage sys}
    (ha : a ∈ representationKernel Stage sys ω) :
    star a ∈ representationKernel Stage sys ω :=
  (star_mem_representationKernel_iff
    Stage sys ω a).2 ha

/-- On a finite-stage observable, the colimit seminorm is exactly the
operator norm of its verified global stage representation. -/
@[simp] theorem representedOperatorRingSeminorm_of
    (i : I) (a : Stage i) :
    representedOperatorRingSeminorm Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a) =
      ‖globalStageRepresentationStarAlgHom
        Stage sys ω i a‖ := by
  rw [representedOperatorRingSeminorm_apply,
    algebraicColimitGNSRepresentation_of]

end CStarStateColimit.Native.FilteredGNSOperatorSeminormKernel
