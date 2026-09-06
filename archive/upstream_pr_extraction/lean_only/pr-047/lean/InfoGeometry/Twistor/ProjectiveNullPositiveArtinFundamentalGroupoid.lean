import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology

/-!
# Fundamental-groupoid readout of the positive Artin configuration action

This owner applies Mathlib's fundamental groupoid functor to the continuous
self-map carried by each element of the positive Artin presented monoid.
Multiplication is read as composition of the induced functors.

These functors arise from global self-maps of unordered configuration space.
They are not loop classes, do not identify a braid group with a fundamental
group, and do not define monodromy.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoid

open CategoryTheory
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The endofunctor of the unordered-configuration fundamental groupoid
induced by one positive Artin configuration self-map. -/
def positiveArtinFundamentalGroupoidMap
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
    (n : ℕ) (a : PositiveArtinMonoid) :
    let _ := unorderedConfigurationTopology Q n
    Functor (FundamentalGroupoid (Unordered Q n))
      (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact FundamentalGroupoid.map
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a)

/-- The identity element of the positive Artin monoid induces the identity
fundamental-groupoid functor. -/
theorem positiveArtinFundamentalGroupoidMap_one
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
    (n : ℕ) :
    let _ := unorderedConfigurationTopology Q n
    positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n 1 =
      𝟭 (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold positiveArtinFundamentalGroupoidMap
  have hmap :
      positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n 1 =
        (@ContinuousMap.id (Unordered Q n)
          (unorderedConfigurationTopology Q n)) := by
    apply ContinuousMap.ext
    intro p
    change positiveArtinConfigurationAction Q ρ hQ hArtin hComm n 1 p = p
    rw [map_one]
    rfl
  rw [hmap]
  exact FundamentalGroupoid.map_id

/-- Positive Artin multiplication becomes composition of the induced
fundamental-groupoid endofunctors.  The order is Mathlib's native functor
composition order for the underlying function-composition action. -/
theorem positiveArtinFundamentalGroupoidMap_mul
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
    (n : ℕ) (a b : PositiveArtinMonoid) :
    let _ := unorderedConfigurationTopology Q n
    positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n (a * b) =
      (positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n b).comp
        (positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n a) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold positiveArtinFundamentalGroupoidMap
  rw [positiveArtinContinuousMap_mul Q ρ hQ hArtin hComm hcont n a b]
  exact FundamentalGroupoid.map_comp
    (X := Unordered Q n) (Y := Unordered Q n) (Z := Unordered Q n)
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a)
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n b)

end InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoid
