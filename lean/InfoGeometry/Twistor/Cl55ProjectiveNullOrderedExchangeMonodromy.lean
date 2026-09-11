import InfoGeometry.Twistor.Cl55ProjectiveNullConfigurationMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy

/-!
# Ordered-exchange monodromy for the `Q55` null boundary

An actual ordered path from a `Q55` null configuration `p` to a finite
reindexing of `p` projects to a loop in the unordered configuration space.
The concrete `Q55` covering monodromy of that loop recovers exactly the
endpoint permutation.

No preferred exchange path, Artin- or spherical-braid-group identification,
Yang--Baxter intertwiner, or anyon interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55ProjectiveNullOrderedExchangeMonodromy

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55ProjectiveNullConfigurationMonodromy
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- The concrete `Q55` covering monodromy of an ordered exchange path is its
endpoint permutation.  The path is supplied explicitly; this theorem does not
assert existence of a canonical or elementary exchange path. -/
@[simp] theorem q55UnorderedCoveringPermutationMonodromy_orderedExchangeLoopClass
    (n : ℕ) (p : Ordered Q55 n) (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q55 n) (orderedConfigurationTopology Q55 n)
      p (permute Q55 n sigma p)) :
    q55UnorderedCoveringPermutationMonodromy n p
        (orderedExchangeLoopClass Q55 n p sigma gamma) = sigma := by
  exact unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass Q55 n
    (q55OrderedConfiguration_locallyCompactSpace n)
    (q55OrderedConfiguration_t2Space n) p sigma gamma

/-- On the canonical labels of the ordered covering fiber, the same exchange
loop acts by left multiplication with its endpoint permutation. -/
@[simp] theorem q55UnorderedDeckLabelMonodromy_orderedExchangeLoopClass_apply
    (n : ℕ) (p : Ordered Q55 n) (sigma tau : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q55 n) (orderedConfigurationTopology Q55 n)
      p (permute Q55 n sigma p)) :
    q55UnorderedDeckLabelMonodromy n p
        (orderedExchangeLoopClass Q55 n p sigma gamma) tau = sigma * tau := by
  rw [q55UnorderedDeckLabelMonodromy_apply,
    q55UnorderedCoveringPermutationMonodromy_orderedExchangeLoopClass]

end InfoGeometry.Twistor.Cl55ProjectiveNullOrderedExchangeMonodromy
