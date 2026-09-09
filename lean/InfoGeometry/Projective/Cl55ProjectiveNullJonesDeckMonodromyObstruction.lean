import InfoGeometry.Projective.ProjectiveNullBoundaryBraidMonodromyComparison
import InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction
import InfoGeometry.Twistor.Cl55ProjectiveNullOrderedExchangeMonodromy
import InfoGeometry.Twistor.ProjectiveNullConfigurationPureMonodromy

/-!
# `Q55` exchange paths, deck monodromy, and the Jones obstruction

Suppose two actual ordered `Q55` null-configuration paths end at the two
adjacent reindexings and their projected loops satisfy the path-level Artin
homotopy.  They define a genuine homomorphism from the native presented `B₃`
to the fundamental group of the unordered configuration space.

This owner proves that composing this homomorphism with the concrete `Q55`
covering monodromy gives exactly the native permutation shadow `B₃ → S₃`.
Consequently, no further homomorphism `S₃ → GL₈(ℂ)` can turn that deck
monodromy into the Jones/Temperley--Lieb representation.

The path and Artin-homotopy inputs are explicit.  No preferred exchange paths,
braid-group identification of the fundamental group, conformal-block local
system, or anyon interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstruction

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidMonodromyComparison
open InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction
open InfoGeometry.Topology.ArtinBraidS3Quotient
open InfoGeometry.Twistor.Cl55ProjectiveNullConfigurationMonodromy
open InfoGeometry.Twistor.Cl55ProjectiveNullOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationExchangeLoop
open InfoGeometry.Twistor.ProjectiveNullConfigurationPureMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- Two actual ordered `Q55` exchange paths with the Artin homotopy recover
the complete native `B₃ → S₃` permutation shadow through covering
monodromy. -/
theorem q55ExchangePermutationMonodromy_eq_braidPermutation
    (p : Ordered Q55 3)
    (gamma0 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma1 p))
    (gamma1 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma2 p))
    (hArtin : ConfigurationLoopArtin Q55 3 (Quotient.mk' p)
      (orderedExchangeLoop Q55 3 p sigma1 gamma0)
      (orderedExchangeLoop Q55 3 p sigma2 gamma1)) :
    (q55UnorderedCoveringPermutationMonodromy 3 p).comp
        (exchangeClassMapOfOrderedPaths Q55 3 p sigma1 sigma2
          gamma0 gamma1 hArtin) = braidPermutation := by
  apply PresentedGroup.ext
  intro g
  cases g
  · change q55UnorderedCoveringPermutationMonodromy 3 p
        (exchangeClassMapOfOrderedPaths Q55 3 p sigma1 sigma2
          gamma0 gamma1 hArtin
            (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup)) = _
    rw [exchangeClassMapOfOrderedPaths, exchangeClassMapOfLoops_sig0]
    change q55UnorderedCoveringPermutationMonodromy 3 p
      (orderedExchangeLoopClass Q55 3 p sigma1 gamma0) = _
    rw [q55UnorderedCoveringPermutationMonodromy_orderedExchangeLoopClass,
      braidPermutation_sig0]
  · change q55UnorderedCoveringPermutationMonodromy 3 p
        (exchangeClassMapOfOrderedPaths Q55 3 p sigma1 sigma2
          gamma0 gamma1 hArtin
            (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup)) = _
    rw [exchangeClassMapOfOrderedPaths, exchangeClassMapOfLoops_sig1]
    change q55UnorderedCoveringPermutationMonodromy 3 p
      (orderedExchangeLoopClass Q55 3 p sigma2 gamma1) = _
    rw [q55UnorderedCoveringPermutationMonodromy_orderedExchangeLoopClass,
      braidPermutation_sig1]

/-- The geometric loop obtained from the square of the first Artin generator.
It is the product of an actual projected ordered exchange loop with itself;
no claim that this is a preferred exchange path is made. -/
def q55FirstExchangeSquare
    (p : Ordered Q55 3)
    (gamma0 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma1 p))
    (gamma1 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma2 p))
    (hArtin : ConfigurationLoopArtin Q55 3 (Quotient.mk' p)
      (orderedExchangeLoop Q55 3 p sigma1 gamma0)
      (orderedExchangeLoop Q55 3 p sigma2 gamma1)) :
    @FundamentalGroup (Unordered Q55 3)
      (unorderedConfigurationTopology Q55 3) (Quotient.mk' p) :=
  exchangeClassMapOfOrderedPaths Q55 3 p sigma1 sigma2
    gamma0 gamma1 hArtin firstGeneratorSquare

/-- The first-exchange square is literally the square of the corresponding
fundamental-group loop. -/
theorem q55FirstExchangeSquare_eq_loop_sq
    (p : Ordered Q55 3)
    (gamma0 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma1 p))
    (gamma1 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma2 p))
    (hArtin : ConfigurationLoopArtin Q55 3 (Quotient.mk' p)
      (orderedExchangeLoop Q55 3 p sigma1 gamma0)
      (orderedExchangeLoop Q55 3 p sigma2 gamma1)) :
    q55FirstExchangeSquare p gamma0 gamma1 hArtin =
      orderedExchangeLoopClass Q55 3 p sigma1 gamma0 *
        orderedExchangeLoopClass Q55 3 p sigma1 gamma0 := by
  rw [q55FirstExchangeSquare, firstGeneratorSquare, map_mul,
    exchangeClassMapOfOrderedPaths, exchangeClassMapOfLoops_sig0]
  rfl

/-- The geometric first-exchange square is pure for the concrete `Q55`
covering: its endpoint-permutation monodromy is trivial. -/
theorem q55FirstExchangeSquare_mem_pureConfigurationLoop
    (p : Ordered Q55 3)
    (gamma0 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma1 p))
    (gamma1 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma2 p))
    (hArtin : ConfigurationLoopArtin Q55 3 (Quotient.mk' p)
      (orderedExchangeLoop Q55 3 p sigma1 gamma0)
      (orderedExchangeLoop Q55 3 p sigma2 gamma1)) :
    q55FirstExchangeSquare p gamma0 gamma1 hArtin ∈
      PureConfigurationLoop Q55 3
        (q55OrderedConfiguration_locallyCompactSpace 3)
        (q55OrderedConfiguration_t2Space 3) p := by
  rw [mem_pureConfigurationLoop_iff]
  have h := congrArg
    (fun f : BoundaryBraidGroup →* Equiv.Perm (Fin 3) =>
      f firstGeneratorSquare)
    (q55ExchangePermutationMonodromy_eq_braidPermutation
      p gamma0 gamma1 hArtin)
  simpa [q55FirstExchangeSquare] using h

/-- No linear representation obtained solely by postcomposing the finite
`Q55` deck-permutation monodromy can equal the Jones `B₃` representation,
even when the two geometric exchange paths satisfy the Artin homotopy. -/
theorem q55JonesRepresentation_not_factor_through_exchangeDeckMonodromy
    (p : Ordered Q55 3)
    (gamma0 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma1 p))
    (gamma1 : @Path (Ordered Q55 3) (orderedConfigurationTopology Q55 3)
      p (permute Q55 3 sigma2 p))
    (hArtin : ConfigurationLoopArtin Q55 3 (Quotient.mk' p)
      (orderedExchangeLoop Q55 3 p sigma1 gamma0)
      (orderedExchangeLoop Q55 3 p sigma2 gamma1)) :
    ¬ ∃ psi : Equiv.Perm (Fin 3) →* GL8,
      (psi.comp (q55UnorderedCoveringPermutationMonodromy 3 p)).comp
          (exchangeClassMapOfOrderedPaths Q55 3 p sigma1 sigma2
            gamma0 gamma1 hArtin) = phi := by
  rintro ⟨psi, hpsi⟩
  apply jonesBraidRepresentation_not_factor_through_permutation
  refine ⟨psi, ?_⟩
  rw [← q55ExchangePermutationMonodromy_eq_braidPermutation
    p gamma0 gamma1 hArtin]
  exact hpsi

end InfoGeometry.Projective.Cl55ProjectiveNullJonesDeckMonodromyObstruction
