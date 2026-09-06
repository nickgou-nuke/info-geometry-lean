import InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
import InfoGeometry.Twistor.ProjectiveNullConfigurationPermutationMonodromy

/-!
# Finite covering monodromy for `Q55` null configurations

The now-unconditional finite permutation covering of ordered over unordered
`Q55` projective-null configurations supplies a concrete representation of the
based fundamental group in `S_n`.

This is deck-permutation monodromy.  It does not identify the source with an
Artin or spherical braid group, select exchange loops, intertwine a
Yang--Baxter operator, or assert anyon data.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55ProjectiveNullConfigurationMonodromy

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- The concrete deck-permutation representation of the fundamental group of
unordered distinct `Q55` null configurations. -/
def q55UnorderedCoveringPermutationMonodromy
    (n : ℕ) (p : Ordered Q55 n) :
    @FundamentalGroup (Unordered Q55 n)
        (unorderedConfigurationTopology Q55 n) (Quotient.mk' p) →*
      Equiv.Perm (Fin n) :=
  unorderedCoveringPermutationMonodromy Q55 n
    (q55OrderedConfiguration_locallyCompactSpace n)
    (q55OrderedConfiguration_t2Space n) p

@[simp] theorem q55UnorderedCoveringPermutationMonodromy_apply
    (n : ℕ) (p : Ordered Q55 n)
    (gamma : @FundamentalGroup (Unordered Q55 n)
      (unorderedConfigurationTopology Q55 n) (Quotient.mk' p)) :
    q55UnorderedCoveringPermutationMonodromy n p gamma =
      (unorderedCoveringDeckPermutation Q55 n
        (q55OrderedConfiguration_locallyCompactSpace n)
        (q55OrderedConfiguration_t2Space n) p gamma).symm :=
  rfl

/-- The same concrete monodromy transported to permutations of the canonical
`S_n` labels of the ordered covering fiber. -/
def q55UnorderedDeckLabelMonodromy
    (n : ℕ) (p : Ordered Q55 n) :
    @FundamentalGroup (Unordered Q55 n)
        (unorderedConfigurationTopology Q55 n) (Quotient.mk' p) →*
      Equiv.Perm (Equiv.Perm (Fin n)) :=
  unorderedConfigurationDeckLabelMonodromy Q55 n
    (q55OrderedConfiguration_locallyCompactSpace n)
    (q55OrderedConfiguration_t2Space n) p

theorem q55UnorderedDeckLabelMonodromy_apply
    (n : ℕ) (p : Ordered Q55 n)
    (gamma : @FundamentalGroup (Unordered Q55 n)
      (unorderedConfigurationTopology Q55 n) (Quotient.mk' p))
    (sigma : Equiv.Perm (Fin n)) :
    q55UnorderedDeckLabelMonodromy n p gamma sigma =
      q55UnorderedCoveringPermutationMonodromy n p gamma * sigma := by
  exact unorderedConfigurationDeckLabelMonodromy_apply Q55 n
    (q55OrderedConfiguration_locallyCompactSpace n)
    (q55OrderedConfiguration_t2Space n) p gamma sigma

end InfoGeometry.Twistor.Cl55ProjectiveNullConfigurationMonodromy
