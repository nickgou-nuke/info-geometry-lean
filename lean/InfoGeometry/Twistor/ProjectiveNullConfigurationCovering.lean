import InfoGeometry.Twistor.ProjectiveNullBoundaryTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Covering.Quotient

/-!
# Finite permutation covering of projective-null configurations

This owner packages finite reindexing as the native left action of
`Equiv.Perm (Fin n)` on ordered distinct-null configurations.  The action is
free, continuous, and properly discontinuous.  Under explicit local
compactness and Hausdorff hypotheses on the ordered carrier, Mathlib's finite
group quotient theorem makes the existing ordered-to-unordered projection a
quotient covering map.

No fundamental-group computation, braid-loop identification, monodromy, or
anyon interpretation is asserted here.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationCovering

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullBoundaryTopology
open InfoGeometry.Twistor.ProjectiveNullArtinBraid
open InfoGeometry.Twistor
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
open Topology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Standard left permutation action, obtained from the repository's
right-reindexing convention by applying the inverse permutation. -/
noncomputable instance orderedPermutationMulAction
    (Q : QuadraticForm K V) (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (Ordered Q n) where
  smul σ p := permute Q n σ.symm p
  one_smul p := by
    change permute Q n (Equiv.refl _) p = p
    exact permute_refl Q n p
  mul_smul σ τ p := by
    apply Subtype.ext
    funext j
    rfl

/-- Distinctness makes the permutation action cancellative also in the group
coordinate: two permutations agreeing on one ordered configuration coincide. -/
instance orderedPermutationIsCancelSMul
    (Q : QuadraticForm K V) (n : ℕ) :
    IsCancelSMul (Equiv.Perm (Fin n)) (Ordered Q n) where
  right_cancel' σ τ p h := by
    have hsymm : σ.symm = τ.symm :=
      permute_eq_of_eq Q n σ.symm τ.symm p h
    simpa using congrArg Equiv.symm hsymm

/-- The finite reindexing action as an explicit homeomorphism of the ordered
distinct-null configuration carrier. -/
noncomputable def orderedPermutationHomeomorph
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    @Homeomorph (Ordered Q n) (Ordered Q n)
      (orderedConfigurationTopology Q n) (orderedConfigurationTopology Q n) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  let e : Ordered Q n ≃ Ordered Q n :=
    { toFun := permute Q n σ
      invFun := permute Q n σ.symm
      left_inv := by
        intro p
        apply Subtype.ext
        funext j
        simp [permute]
      right_inv := by
        intro p
        apply Subtype.ext
        funext j
        simp [permute] }
  exact Homeomorph.mk e
    (permute_continuous Q n σ)
    (permute_continuous Q n σ.symm)

@[simp] theorem orderedPermutationHomeomorph_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : Ordered Q n) :
    orderedPermutationHomeomorph Q n σ p = permute Q n σ p :=
  rfl

@[simp] theorem orderedPermutation_smul_eq_homeomorph
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : Ordered Q n) :
    σ • p = orderedPermutationHomeomorph Q n σ.symm p := by
  rfl

/-- Composition of deck homeomorphisms follows the native permutation
composition convention (`σ.trans τ` acts as `τ` after `σ`). -/
theorem orderedPermutationHomeomorph_comp
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) (p : Ordered Q n) :
    let _inst : TopologicalSpace (Ordered Q n) :=
      orderedConfigurationTopology Q n
    orderedPermutationHomeomorph Q n σ
        (orderedPermutationHomeomorph Q n τ p) =
      orderedPermutationHomeomorph Q n (σ.trans τ) p := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  change permute Q n σ (permute Q n τ p) = permute Q n (σ.trans τ) p
  exact permute_comp Q n σ τ p

/-- Equality in the existing unordered quotient is exactly membership in an
orbit of the native left permutation action. -/
theorem unorderedProjection_eq_iff_mem_orbit
    (Q : QuadraticForm K V) (n : ℕ) (p q : Ordered Q n) :
    (@Quotient.mk' (Ordered Q n) (reindexSetoid Q n) p =
        @Quotient.mk' (Ordered Q n) (reindexSetoid Q n) q) ↔
      p ∈ MulAction.orbit (Equiv.Perm (Fin n)) q := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro hpq
    obtain ⟨σ, hσ⟩ := Quotient.exact hpq
    refine ⟨σ, ?_⟩
    change permute Q n σ.symm q = p
    rw [hσ, permute_comp]
    simp
  · rintro ⟨σ, hσ⟩
    apply Quotient.sound
    refine ⟨σ, ?_⟩
    change q = permute Q n σ p
    rw [← hσ]
    change q = permute Q n σ (permute Q n σ.symm q)
    rw [permute_comp]
    simp

/-- For a Hausdorff carrier, the locus of pairwise-distinct finite tuples is
open in the finite function space. -/
theorem pairwiseDistinct_isOpen
    {X : Type*} [TopologicalSpace X] [T2Space X] (n : ℕ) :
    IsOpen {f : Fin n → X | PairwiseDistinct f} := by
  rw [show {f : Fin n → X | PairwiseDistinct f} =
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_h : i ≠ j), {f | f i ≠ f j} by
    ext f
    simp [PairwiseDistinct]]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_ne_fun (continuous_apply i) (continuous_apply j)

/-- Hausdorffness of the null boundary passes to its ordered configuration
carrier with the named induced topology. -/
theorem orderedConfiguration_t2Space
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hT2 : @T2Space (TwistorSpace Q) (nullBoundaryTopology Q)) :
    @T2Space (Ordered Q n) (orderedConfigurationTopology Q n) := by
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : T2Space (TwistorSpace Q) := hT2
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  exact Topology.IsEmbedding.subtypeVal.t2Space

/-- Local compactness passes from a Hausdorff null boundary to ordered
distinct configurations because the distinctness locus is open in a finite
product. -/
theorem orderedConfiguration_locallyCompactSpace
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (TwistorSpace Q) (nullBoundaryTopology Q))
    (hT2 : @T2Space (TwistorSpace Q) (nullBoundaryTopology Q)) :
    @LocallyCompactSpace (Ordered Q n) (orderedConfigurationTopology Q n) := by
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : LocallyCompactSpace (TwistorSpace Q) := hLC
  letI : T2Space (TwistorSpace Q) := hT2
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  exact (pairwiseDistinct_isOpen n).locallyCompactSpace

/-- Under the precise local hypotheses required by Mathlib, the canonical
ordered-to-unordered projection is a finite quotient covering map with the
canonical quotient action of `Equiv.Perm (Fin n)`.  This does not identify
the full deck-transformation group without an additional classification
theorem. -/
theorem unorderedProjection_isQuotientCoveringMap
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n)) :
    let _ := orderedConfigurationTopology Q n
    let _ := unorderedConfigurationTopology Q n
    IsQuotientCoveringMap
      (@Quotient.mk' (Ordered Q n) (reindexSetoid Q n))
      (Equiv.Perm (Fin n)) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  letI : LocallyCompactSpace (Ordered Q n) := hLC
  letI : T2Space (Ordered Q n) := hT2
  letI : ContinuousConstSMul (Equiv.Perm (Fin n)) (Ordered Q n) :=
    { continuous_const_smul := fun σ => permute_continuous Q n σ.symm }
  change IsQuotientCoveringMap
    (@Quotient.mk' (Ordered Q n) (reindexSetoid Q n))
    (Equiv.Perm (Fin n))
  exact (unorderedProjection_isQuotientMap Q n).isQuotientCoveringMap_of_properlyDiscontinuousSMul
        (fun {p q} => unorderedProjection_eq_iff_mem_orbit Q n p q)

/-- The quotient-covering hypotheses can be supplied entirely on the
projective null boundary; the ordered configuration hypotheses are derived
from finite-product and open-subspace topology. -/
theorem unorderedProjection_isQuotientCoveringMap_of_nullBoundary
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (TwistorSpace Q) (nullBoundaryTopology Q))
    (hT2 : @T2Space (TwistorSpace Q) (nullBoundaryTopology Q)) :
    let _ := orderedConfigurationTopology Q n
    let _ := unorderedConfigurationTopology Q n
    IsQuotientCoveringMap
      (@Quotient.mk' (Ordered Q n) (reindexSetoid Q n))
      (Equiv.Perm (Fin n)) := by
  exact unorderedProjection_isQuotientCoveringMap Q n
    (orderedConfiguration_locallyCompactSpace Q n hLC hT2)
    (orderedConfiguration_t2Space Q n hT2)

/-- Ambient projective Hausdorffness and local compactness, together with
continuity of the quadratic form, supply all hypotheses for the finite
configuration quotient-covering theorem. -/
theorem unorderedProjection_isQuotientCoveringMap_of_projectivization
    [TopologicalSpace K] [T2Space K] [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hQ : Continuous (Q : V → K))
    (hLC : @LocallyCompactSpace (ℙ K V)
      (projectivizationQuotientTopology (K := K) (V := V)))
    (hT2 : @T2Space (ℙ K V)
      (projectivizationQuotientTopology (K := K) (V := V))) :
    let _ := orderedConfigurationTopology Q n
    let _ := unorderedConfigurationTopology Q n
    IsQuotientCoveringMap
      (@Quotient.mk' (Ordered Q n) (reindexSetoid Q n))
      (Equiv.Perm (Fin n)) := by
  exact unorderedProjection_isQuotientCoveringMap_of_nullBoundary Q n
    (nullBoundary_locallyCompactSpace Q hQ hLC)
    (nullBoundary_t2Space Q hT2)

end InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
