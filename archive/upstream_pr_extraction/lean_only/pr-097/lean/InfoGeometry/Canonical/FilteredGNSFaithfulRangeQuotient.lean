import InfoGeometry.Canonical.FilteredGNSOperatorSeminormKernel

/-!
# Faithful represented range of the filtered GNS star-colimit

The algebraic filtered star-colimit factors surjectively through the concrete
star subalgebra given by the range of its global GNS representation.  Equality
in this represented range is exactly equality modulo the representation
kernel, equivalently vanishing of the pulled-back operator seminorm on the
difference.

The represented range embeds faithfully and densely into the concrete
represented C-star closure.  This is the native first-isomorphism interface
available before constructing any separate star structure on an ideal
quotient.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSOperatorSeminormKernel

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

/-- Concrete algebraic operator range of the global filtered GNS
representation. -/
abbrev representedAlgebraicRange :=
  (algebraicColimitGNSRepresentation Stage sys ω).range

/-- Canonical surjective star-algebra map from the raw algebraic colimit onto
its represented operator range. -/
def algebraicColimitRangeRestrict :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      representedAlgebraicRange Stage sys ω :=
  (algebraicColimitGNSRepresentation Stage sys ω).rangeRestrict

@[simp] theorem algebraicColimitRangeRestrict_coe
    (a : AlgebraicStarDirectLimit Stage sys) :
    (algebraicColimitRangeRestrict Stage sys ω a :
      GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) =
      algebraicColimitGNSRepresentation Stage sys ω a :=
  rfl

theorem algebraicColimitRangeRestrict_surjective :
    Function.Surjective
      (algebraicColimitRangeRestrict Stage sys ω) :=
  (algebraicColimitGNSRepresentation
    Stage sys ω).toAlgHom.rangeRestrict_surjective

/-- Two algebraic-colimit elements define the same represented operator
exactly when their difference belongs to the representation kernel. -/
theorem algebraicColimitRangeRestrict_eq_iff_sub_mem_kernel
    (a b : AlgebraicStarDirectLimit Stage sys) :
    algebraicColimitRangeRestrict Stage sys ω a =
        algebraicColimitRangeRestrict Stage sys ω b ↔
      a - b ∈ representationKernel Stage sys ω := by
  rw [mem_representationKernel_iff]
  constructor
  · intro h
    rw [map_sub]
    exact sub_eq_zero.mpr (Subtype.ext_iff.mp h)
  · intro h
    apply Subtype.ext
    exact sub_eq_zero.mp ((map_sub _ a b).symm.trans h)

/-- The pulled-back operator seminorm separates precisely the represented
range classes. -/
theorem representedOperatorRingSeminorm_sub_eq_zero_iff
    (a b : AlgebraicStarDirectLimit Stage sys) :
    representedOperatorRingSeminorm Stage sys ω (a - b) = 0 ↔
      algebraicColimitRangeRestrict Stage sys ω a =
        algebraicColimitRangeRestrict Stage sys ω b := by
  rw [representedOperatorRingSeminorm_eq_zero_iff,
    ← algebraicColimitRangeRestrict_eq_iff_sub_mem_kernel]

/-- Faithful inclusion of the represented algebraic range into its
operator-norm C-star closure. -/
def representedAlgebraicRangeInclusion :
    representedAlgebraicRange Stage sys ω →⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω :=
  StarSubalgebra.inclusion
    (StarSubalgebra.le_topologicalClosure
      (representedAlgebraicRange Stage sys ω))

theorem representedAlgebraicRangeInclusion_injective :
    Function.Injective
      (representedAlgebraicRangeInclusion Stage sys ω) :=
  StarSubalgebra.inclusion_injective
    (StarSubalgebra.le_topologicalClosure
      (representedAlgebraicRange Stage sys ω))

/-- The faithful algebraic range is dense in the represented C-star closure
by the definition of that closure. -/
theorem representedAlgebraicRangeInclusion_denseRange :
    DenseRange
      (representedAlgebraicRangeInclusion Stage sys ω) := by
  change DenseRange
    (Set.inclusion
      (StarSubalgebra.le_topologicalClosure
        (representedAlgebraicRange Stage sys ω)))
  simp [-SetLike.coe_sort_coe]

end CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
