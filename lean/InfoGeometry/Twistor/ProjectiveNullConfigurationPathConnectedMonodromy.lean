import InfoGeometry.Twistor.ProjectiveNullConfigurationPureMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Permutation monodromy for path-connected ordered null configurations

If the ordered projective-null configuration carrier is path connected, then
every finite reindexing of a base configuration is joined to it by an ordered
path.  Projecting such a path to the unordered quotient gives a based loop
whose covering monodromy is the prescribed permutation.  Consequently the
permutation monodromy is surjective and the quotient by its pure kernel is
canonically the full symmetric group.

The path-connectedness hypothesis is explicit.  This owner does not prove it
for a particular null boundary, and it does not identify the fundamental group
with an Artin, pure-braid, or spherical-braid group.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationPathConnectedMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationPureMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Path connectedness of the ordered configuration carrier realizes every
deck permutation by a projected ordered path. -/
theorem unorderedCoveringPermutationMonodromy_surjective_of_pathConnected
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (hPC : @PathConnectedSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    Function.Surjective
      (unorderedCoveringPermutationMonodromy Q n hLC hT2 p) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : PathConnectedSpace (Ordered Q n) := hPC
  intro σ
  let gamma : Path p (permute Q n σ p) :=
    Joined.somePath
      ((pathConnectedSpace_iff (Ordered Q n)).mp inferInstance |>.2 p
        (permute Q n σ p))
  exact ⟨orderedExchangeLoopClass Q n p σ gamma,
    unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass
      Q n hLC hT2 p σ gamma⟩

/-- Under explicit path connectedness, the image of permutation monodromy is
the whole symmetric group. -/
theorem unorderedCoveringPermutationMonodromy_range_eq_top_of_pathConnected
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (hPC : @PathConnectedSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    (unorderedCoveringPermutationMonodromy Q n hLC hT2 p).range = ⊤ := by
  exact MonoidHom.range_eq_top.mpr
    (unorderedCoveringPermutationMonodromy_surjective_of_pathConnected
      Q n hLC hT2 hPC p)

/-- First-isomorphism theorem with full target: when the ordered carrier is
path connected, based loops modulo permutation-trivial monodromy are the full
finite symmetric group of labels. -/
def configurationLoopQuotientEquivPerm_of_pathConnected
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (hPC : @PathConnectedSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    (@FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p)) ⧸
        PureConfigurationLoop Q n hLC hT2 p ≃*
      Equiv.Perm (Fin n) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (unorderedCoveringPermutationMonodromy Q n hLC hT2 p)
    (unorderedCoveringPermutationMonodromy_surjective_of_pathConnected
      Q n hLC hT2 hPC p)

end InfoGeometry.Twistor.ProjectiveNullConfigurationPathConnectedMonodromy
