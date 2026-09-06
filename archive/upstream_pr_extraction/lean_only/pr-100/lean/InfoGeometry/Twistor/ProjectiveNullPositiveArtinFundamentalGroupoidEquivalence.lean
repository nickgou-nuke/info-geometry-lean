import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroup
import InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoid
import InfoGeometry.Twistor.ProjectiveNullPositiveArtinHomeomorph

/-!
# Fundamental-groupoid equivalence from the positive Artin configuration action

Every concrete positive Artin configuration map is already a homeomorphism.
This owner applies Mathlib's native
`FundamentalGroupoidFunctor.equivOfHomotopyEquiv` construction to obtain an
autoequivalence of the unordered-configuration fundamental groupoid.

This is an equivalence induced by a global homeomorphism of configuration
space.  It is not a loop class, a computation of the fundamental group, a
monodromy representation, or an anyon statement.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoidEquivalence

open CategoryTheory
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroup
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinHomeomorph
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The fundamental-groupoid autoequivalence induced by the homeomorphic
positive Artin action on unordered projective-null configurations. -/
def positiveArtinFundamentalGroupoidEquivalence
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid) :
    let _ := unorderedConfigurationTopology Q n
    FundamentalGroupoid (Unordered Q n) ≌ FundamentalGroupoid (Unordered Q n) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let h : @Homeomorph (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n) :=
    positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
      hcont hcont_inv n a
  let he : @ContinuousMap.HomotopyEquiv (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n) :=
    @Homeomorph.toHomotopyEquiv (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n) h
  exact @FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (Unordered Q n) (Unordered Q n)
    (unorderedConfigurationTopology Q n)
    (unorderedConfigurationTopology Q n) he

/-- The forward functor of the autoequivalence is exactly the previously
constructed fundamental-groupoid map. -/
theorem positiveArtinFundamentalGroupoidEquivalence_functor
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid) :
    let _ := unorderedConfigurationTopology Q n
    (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
      hcont hcont_inv n a).functor =
        positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n a := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let h : @Homeomorph (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n) :=
    positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
      hcont hcont_inv n a
  unfold positiveArtinFundamentalGroupoidEquivalence
  change FundamentalGroupoid.map
      (h : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)) =
    FundamentalGroupoid.map
      (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a)
  congr 1

/-- The identity element induces the identity functor under the fundamental-
groupoid equivalence. -/
theorem positiveArtinFundamentalGroupoidEquivalence_functor_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) :
    let _ := unorderedConfigurationTopology Q n
    (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
      hcont hcont_inv n 1).functor =
      𝟭 (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rw [positiveArtinFundamentalGroupoidEquivalence_functor,
    positiveArtinFundamentalGroupoidMap_one]

/-- The inverse functor is the fundamental-groupoid map of the inverse
homeomorphism.  This is the concrete inverse readout; it is not a loop or
monodromy statement. -/
theorem positiveArtinFundamentalGroupoidEquivalence_inverse
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid) :
    let _ := unorderedConfigurationTopology Q n
    (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
      hcont hcont_inv n a).inverse =
      FundamentalGroupoid.map
        ((positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
          hcont hcont_inv n a).symm :
          @ContinuousMap (Unordered Q n) (Unordered Q n)
            (unorderedConfigurationTopology Q n)
            (unorderedConfigurationTopology Q n)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let h : @Homeomorph (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n) :=
    positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
      hcont hcont_inv n a
  unfold positiveArtinFundamentalGroupoidEquivalence
  change FundamentalGroupoid.map
      (h.symm : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)) =
    FundamentalGroupoid.map
      (h.symm : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n))
  rfl

/-- The inverse functor is also the identity functor at the identity element. -/
theorem positiveArtinFundamentalGroupoidEquivalence_inverse_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) :
    let _ := unorderedConfigurationTopology Q n
    (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
      hcont hcont_inv n 1).inverse =
      𝟭 (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rw [positiveArtinFundamentalGroupoidEquivalence_inverse,
    positiveArtinConfigurationActionHomeomorph_one]
  simpa using
    (FundamentalGroupoid.map_id (X := Unordered Q n))

theorem positiveArtinFundamentalGroupoidEquivalence_functor_mul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a b : PositiveArtinMonoid) :
    let _ := unorderedConfigurationTopology Q n
    (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
      hcont hcont_inv n (a * b)).functor =
      (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
        hcont hcont_inv n b).functor.comp
        (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
          hcont hcont_inv n a).functor := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rw [positiveArtinFundamentalGroupoidEquivalence_functor,
    positiveArtinFundamentalGroupoidEquivalence_functor,
    positiveArtinFundamentalGroupoidEquivalence_functor,
    positiveArtinFundamentalGroupoidMap_mul]

/-- A positive Artin configuration homeomorphism induces a multiplicative
equivalence between the fundamental groups at a point and at its image.
The basepoint is deliberately allowed to move. -/
def positiveArtinFundamentalGroupMulEquiv
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid) (p : Unordered Q n) :
    @FundamentalGroup (Unordered Q n) (unorderedConfigurationTopology Q n) p ≃*
      @FundamentalGroup (Unordered Q n) (unorderedConfigurationTopology Q n)
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let e := positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
    hcont hcont_inv n a
  exact e.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk p)

/-- Pointwise, the multiplicative group equivalence is the fundamental-group
homomorphism already induced by the same configuration homeomorphism. -/
theorem positiveArtinFundamentalGroupMulEquiv_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid) (p : Unordered Q n)
    (q : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p) :
    positiveArtinFundamentalGroupMulEquiv Q ρ hQ hArtin hComm
      hcont hcont_inv n a p q =
      positiveArtinFundamentalGroupMap Q ρ hQ hArtin hComm hcont n a p q := by
  rfl

end InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoidEquivalence
