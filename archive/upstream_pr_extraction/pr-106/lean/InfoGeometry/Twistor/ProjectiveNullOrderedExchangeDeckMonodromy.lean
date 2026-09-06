import InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
import InfoGeometry.Twistor.ProjectiveNullConfigurationPermutationLinearMonodromy

/-!
# Deck monodromy of ordered projective-null exchange paths

An ordered path from a configuration `p` to a finite reindexing of `p`
projects to a based loop in the unordered quotient.  This owner proves that
covering monodromy lifts that loop back to the original ordered path and hence
recovers its endpoint permutation.

The resulting permutation is `sigma.symm` because the repository's native
left action is defined by `sigma • p = permute sigma.symm p`.  No Artin- or
spherical-braid-group identification, preferred exchange path, conformal-block
local system, or anyon interpretation is asserted.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Lifting the unordered loop obtained from an ordered exchange path recovers
the endpoint of that original ordered path. -/
theorem unorderedCoveringMonodromyEndpoint_orderedExchangeLoopClass
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (sigma : Equiv.Perm (Fin n))
  (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) :
    unorderedCoveringMonodromyEndpoint Q n hLC hT2 p
        (orderedExchangeLoopClass Q n p sigma gamma) =
      permute Q n sigma p := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let cov := (unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap
  let projected : @Path (Unordered Q n) (unorderedConfigurationTopology Q n)
      (Quotient.mk' p) (Quotient.mk' p) := orderedExchangeLoop Q n p sigma gamma
  have hstart : (projected : C(unitInterval, Unordered Q n)) 0 = Quotient.mk' p :=
    projected.source
  change (cov.liftPath projected p hstart) 1 = permute Q n sigma p
  have hlift : gamma = cov.liftPath projected p hstart := by
    apply (cov.eq_liftPath_iff' hstart).2
    constructor
    · funext t
      exact (orderedExchangeLoop_apply Q n p sigma gamma t).symm
    · exact gamma.source
  rw [← hlift]
  exact gamma.target

/-- The deck-permutation monodromy of a projected ordered exchange path is
the permutation labelling its endpoint, expressed in the native left-action
convention. -/
theorem unorderedCoveringDeckPermutation_orderedExchangeLoopClass
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) :
    unorderedCoveringDeckPermutation Q n hLC hT2 p
        (orderedExchangeLoopClass Q n p sigma gamma) = sigma.symm := by
  symm
  apply unorderedCoveringDeckPermutation_unique Q n hLC hT2 p
  change permute Q n sigma p = _
  exact unorderedCoveringMonodromyEndpoint_orderedExchangeLoopClass
    Q n hLC hT2 p sigma gamma |>.symm

/-- In the ordinary symmetric-group convention, the covering monodromy of a
projected ordered exchange path is exactly its endpoint permutation label. -/
@[simp] theorem unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) :
    unorderedCoveringPermutationMonodromy Q n hLC hT2 p
        (orderedExchangeLoopClass Q n p sigma gamma) = sigma := by
  change (unorderedCoveringDeckPermutation Q n hLC hT2 p
      (orderedExchangeLoopClass Q n p sigma gamma)).symm = sigma
  rw [unorderedCoveringDeckPermutation_orderedExchangeLoopClass]
  rfl

/-- The transported finite-fiber monodromy sends an ordered exchange path to
the corresponding left permutation of its canonical fiber labels.  This is a
covering-monodromy readout, not an assertion that the path is an elementary
Artin exchange or that the resulting representation is an anyon theory. -/
@[simp] theorem unorderedConfigurationDeckLabelMonodromy_orderedExchangeLoopClass_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (sigma τ : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) :
    unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p
        (orderedExchangeLoopClass Q n p sigma gamma) τ = sigma * τ := by
  rw [unorderedConfigurationDeckLabelMonodromy_apply]
  rw [unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass]

/-- Linearized covering monodromy sends a basis state labelled by `tau` to
the basis state labelled by `sigma * tau` for every ordered exchange path
ending at `sigma • p`.  This is a finite covering-monodromy readout, not an
Artin- or spherical-braid-group identification. -/
@[simp] theorem
    unorderedCoveringPermutationLinearMonodromy_orderedExchangeLoopClass_single
    (R : Type*) [Semiring R] [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (sigma tau : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) (r : R) :
    (unorderedCoveringPermutationLinearMonodromy R Q n hLC hT2 p
        (orderedExchangeLoopClass Q n p sigma gamma) :
      DeckPermutationModule R n →ₗ[R] DeckPermutationModule R n)
        (Finsupp.single tau r) = Finsupp.single (sigma * tau) r := by
  rw [unorderedCoveringPermutationLinearMonodromy_single,
    unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass]

end InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
