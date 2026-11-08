import InfoGeometry.Twistor.ProjectiveNullConfigurationPermutationMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Linearized permutation monodromy of projective-null configurations

The finite covering monodromy already gives an honest permutation
representation of the based fundamental group in `S_n`.  This owner applies
the native left-regular action of `S_n` on its free `R`-module and obtains a
literal general-linear representation `π₁(UConf n) →* GL_R(R[S_n])`.

This is the linearization of finite covering-space monodromy.  It does not
identify the source with an Artin or spherical braid group, construct a
conformal-block local system, or assert an anyon interpretation.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The free coefficient module on the finite deck-label set `S_n`. -/
abbrev DeckPermutationModule (R : Type*) [Semiring R] (n : ℕ) :=
  Equiv.Perm (Fin n) →₀ R

/-- Left multiplication by a deck permutation, linearly extended from the
canonical basis of the free deck-label module. -/
def deckPermutationBasisLinearEquiv
    (R : Type*) [Semiring R] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    DeckPermutationModule R n ≃ₗ[R] DeckPermutationModule R n :=
  Finsupp.domLCongr (Equiv.mulLeft σ)

@[simp] theorem deckPermutationBasisLinearEquiv_single
    (R : Type*) [Semiring R] (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) (r : R) :
    deckPermutationBasisLinearEquiv R n σ (Finsupp.single τ r) =
      Finsupp.single (σ * τ) r := by
  exact Finsupp.domLCongr_single (Equiv.mulLeft σ) τ r

theorem deckPermutationBasisLinearEquiv_mul
    (R : Type*) [Semiring R] (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) :
    deckPermutationBasisLinearEquiv R n (σ * τ) =
      deckPermutationBasisLinearEquiv R n σ *
        deckPermutationBasisLinearEquiv R n τ := by
  apply LinearEquiv.ext
  intro x
  refine Finsupp.induction x ?_ ?_
  · rfl
  · intro a b f ha hb ih
    have hsingle :
        deckPermutationBasisLinearEquiv R n (σ * τ) (Finsupp.single a b) =
          (deckPermutationBasisLinearEquiv R n σ *
              deckPermutationBasisLinearEquiv R n τ) (Finsupp.single a b) := by
      rw [deckPermutationBasisLinearEquiv_single]
      change Finsupp.single ((σ * τ) * a) b =
        deckPermutationBasisLinearEquiv R n σ
          (deckPermutationBasisLinearEquiv R n τ (Finsupp.single a b))
      rw [deckPermutationBasisLinearEquiv_single,
        deckPermutationBasisLinearEquiv_single, mul_assoc]
    rw [map_add, map_add, hsingle, ih]

/-- The native left-regular general-linear representation of the deck-label
group on its free coefficient module. -/
def deckPermutationLinearRepresentation
    (R : Type*) [Semiring R] (n : ℕ) :
    Equiv.Perm (Fin n) →*
      LinearMap.GeneralLinearGroup R (DeckPermutationModule R n) where
  toFun σ := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (deckPermutationBasisLinearEquiv R n σ)
  map_one' := by
    have hone : deckPermutationBasisLinearEquiv R n 1 = 1 := by
      apply LinearEquiv.ext
      intro x
      refine Finsupp.induction x rfl ?_
      intro a b f ha hb ih
      rw [map_add, deckPermutationBasisLinearEquiv_single, ih, one_mul]
      rfl
    apply Units.ext
    exact congrArg LinearEquiv.toLinearMap hone
  map_mul' σ τ := by
    apply Units.ext
    exact congrArg LinearEquiv.toLinearMap
      (deckPermutationBasisLinearEquiv_mul R n σ τ)

/-- The concrete GL-valued monodromy obtained by composing covering
permutation monodromy with its left-regular linear representation. -/
def unorderedCoveringPermutationLinearMonodromy
    (R : Type*) [Semiring R] [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup R (DeckPermutationModule R n) :=
  (deckPermutationLinearRepresentation R n).comp
    (unorderedCoveringPermutationMonodromy Q n hLC hT2 p)

/-- On the canonical basis, linearized covering monodromy is left
multiplication by the normalized endpoint permutation. -/
@[simp] theorem unorderedCoveringPermutationLinearMonodromy_single
    (R : Type*) [Semiring R] [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (τ : Equiv.Perm (Fin n)) (r : R) :
    (unorderedCoveringPermutationLinearMonodromy R Q n hLC hT2 p γ :
        DeckPermutationModule R n →ₗ[R] DeckPermutationModule R n)
        (Finsupp.single τ r) =
      Finsupp.single
        (unorderedCoveringPermutationMonodromy Q n hLC hT2 p γ * τ) r := by
  exact deckPermutationBasisLinearEquiv_single R n _ τ r

end InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
