import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Nontriviality of normalized filtered GNS Hilbert colimits

A normalized positive state has a nonzero GNS vacuum: the class of the
algebra unit has norm-square one.  Since every stage embeds isometrically
into the global filtered GNS Hilbert colimit, the global completion is
nontrivial as well.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSHilbertNontrivial

set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit

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

/-- The GNS class of the unit is nonzero for every normalized stage state. -/
theorem stageGNSVacuum_ne_zero
    (i : I) :
    ((((ω.state i).functional.toPreGNS 1 :
        (ω.state i).functional.PreGNS) :
      (ω.state i).functional.GNS)) ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [UniformSpace.Completion.norm_coe, norm_zero] at hn
  have hs :=
    (ω.state i).functional.preGNS_norm_sq
      ((ω.state i).functional.toPreGNS 1)
  rw [hn] at hs
  norm_num at hs

/-- A chosen stage vacuum embedded in the global filtered GNS Hilbert
colimit. -/
def globalGNSVacuum
    (i : I) :
    GNSHilbertColimit Stage sys ω :=
  gnsStageToHilbertColimit Stage sys ω i
    (((ω.state i).functional.toPreGNS 1 :
        (ω.state i).functional.PreGNS) :
      (ω.state i).functional.GNS)

theorem globalGNSVacuum_ne_zero
    (i : I) :
    globalGNSVacuum Stage sys ω i ≠ 0 := by
  intro h
  apply stageGNSVacuum_ne_zero Stage sys ω i
  exact
    (gnsStageToHilbertColimit
      Stage sys ω i).injective
      (by simpa [globalGNSVacuum] using h)

/-- Every normalized filtered GNS Hilbert colimit is nontrivial. -/
instance globalGNSHilbertColimitNontrivial :
    Nontrivial (GNSHilbertColimit Stage sys ω) := by
  let i : I := Classical.choice inferInstance
  exact
    ⟨⟨globalGNSVacuum Stage sys ω i, 0,
      globalGNSVacuum_ne_zero Stage sys ω i⟩⟩

end CStarStateColimit.Native.FilteredGNSHilbertNontrivial
