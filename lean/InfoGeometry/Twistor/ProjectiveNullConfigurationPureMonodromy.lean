import InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pure covering monodromy of projective-null configurations

The finite covering supplies a canonical endpoint-permutation representation
of the based fundamental group.  This owner defines its kernel and proves:

* a projected ordered path is in the kernel exactly when its endpoint
  permutation is trivial;
* the left-regular linearization is faithful over every nontrivial semiring,
  so its GL-valued monodromy has exactly the same kernel;
* the quotient by this kernel is canonically equivalent to the actual image
  of permutation monodromy.

`PureConfigurationLoop` means permutation-trivial covering monodromy.  No
identification with a classical pure braid group, Artin group, or spherical
braid group is asserted.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationPureMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Based loops whose finite covering monodromy has trivial endpoint
permutation.  This is a kernel definition, not a pure-braid identification. -/
def PureConfigurationLoop
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    Subgroup (@FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :=
  (unorderedCoveringPermutationMonodromy Q n hLC hT2 p).ker

@[simp] theorem mem_pureConfigurationLoop_iff
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    γ ∈ PureConfigurationLoop Q n hLC hT2 p ↔
      unorderedCoveringPermutationMonodromy Q n hLC hT2 p γ = 1 := by
  exact MonoidHom.mem_ker

/-- A projected ordered path is permutation-pure exactly when its endpoint
label is the identity permutation. -/
@[simp] theorem orderedExchangeLoopClass_mem_pureConfigurationLoop_iff
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (σ : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n σ p)) :
    orderedExchangeLoopClass Q n p σ gamma ∈
        PureConfigurationLoop Q n hLC hT2 p ↔ σ = 1 := by
  rw [mem_pureConfigurationLoop_iff,
    unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass]

/-- The left-regular action on the free deck-label module is faithful over a
nontrivial coefficient semiring. -/
theorem deckPermutationLinearRepresentation_injective
    (R : Type*) [Semiring R] [Nontrivial R] (n : ℕ) :
    Function.Injective (deckPermutationLinearRepresentation R n) := by
  intro σ τ h
  have hs := congrArg
    (fun g : LinearMap.GeneralLinearGroup R (DeckPermutationModule R n) =>
      (g : DeckPermutationModule R n →ₗ[R] DeckPermutationModule R n)
        (Finsupp.single 1 1)) h
  change deckPermutationBasisLinearEquiv R n σ (Finsupp.single 1 1) =
    deckPermutationBasisLinearEquiv R n τ (Finsupp.single 1 1) at hs
  rw [deckPermutationBasisLinearEquiv_single,
    deckPermutationBasisLinearEquiv_single, mul_one, mul_one] at hs
  exact Finsupp.single_left_injective one_ne_zero hs

/-- Faithful linearization detects precisely the permutation-pure loops. -/
theorem unorderedCoveringPermutationLinearMonodromy_eq_one_iff_pure
    (R : Type*) [Semiring R] [Nontrivial R] [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedCoveringPermutationLinearMonodromy R Q n hLC hT2 p γ = 1 ↔
      γ ∈ PureConfigurationLoop Q n hLC hT2 p := by
  rw [mem_pureConfigurationLoop_iff]
  constructor
  · intro h
    apply deckPermutationLinearRepresentation_injective R n
    simpa using h
  · intro h
    change deckPermutationLinearRepresentation R n
      (unorderedCoveringPermutationMonodromy Q n hLC hT2 p γ) = 1
    rw [h, map_one]

/-- Subgroup form of the equality between the GL-monodromy kernel and the
permutation-monodromy kernel. -/
theorem unorderedCoveringPermutationLinearMonodromy_ker_eq_pure
    (R : Type*) [Semiring R] [Nontrivial R] [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    (unorderedCoveringPermutationLinearMonodromy R Q n hLC hT2 p).ker =
      PureConfigurationLoop Q n hLC hT2 p := by
  ext γ
  rw [MonoidHom.mem_ker,
    unorderedCoveringPermutationLinearMonodromy_eq_one_iff_pure]

instance pureConfigurationLoop_normal
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    (PureConfigurationLoop Q n hLC hT2 p).Normal := by
  change (unorderedCoveringPermutationMonodromy Q n hLC hT2 p).ker.Normal
  infer_instance

/-- First-isomorphism readout: based loops modulo permutation-trivial
monodromy are canonically the actual subgroup of `S_n` reached by the
covering.  Surjectivity onto all of `S_n` is deliberately not assumed. -/
def configurationLoopQuotientEquivPermutationMonodromyRange
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    (@FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p)) ⧸
        PureConfigurationLoop Q n hLC hT2 p ≃*
      (unorderedCoveringPermutationMonodromy Q n hLC hT2 p).range :=
  QuotientGroup.quotientKerEquivRange
    (unorderedCoveringPermutationMonodromy Q n hLC hT2 p)

end InfoGeometry.Twistor.ProjectiveNullConfigurationPureMonodromy
