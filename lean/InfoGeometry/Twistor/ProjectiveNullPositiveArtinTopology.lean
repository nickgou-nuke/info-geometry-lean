import InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology

/-!
# Topological positive Artin action on projective-null configurations

This owner proves that the native `PresentedMonoid` action constructed in
`ProjectiveNullPositiveArtinMonoid` consists of continuous maps.  It then
packages each action map as a `ContinuousMap` on the unordered projective-null
configuration space.

This remains an action by global maps of configuration space.  It does not
identify positive Artin elements with paths or loops and does not construct
monodromy.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology

open scoped LinearAlgebra.Projectivization

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every element of the presented positive Artin monoid acts continuously on
the unordered projective-null configuration space. -/
theorem positiveArtinConfigurationAction_continuous
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
    @Continuous (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n)
      (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  refine PresentedMonoid.inductionOn a ?_
  intro w
  have hreadout :
      positiveArtinConfigurationAction Q ρ hQ hArtin hComm n
          (PresentedMonoid.mk PositiveArtinRelation w) =
        mapUnorderedConfigurationWord Q ρ hQ n w.toList := by
    rw [← FreeMonoid.ofList_toList w]
    exact positiveArtinConfigurationAction_word Q ρ hQ hArtin hComm n w.toList
  have hw := mapUnorderedConfigurationWord_continuous
    Q ρ hQ n hcont w.toList
  rw [hreadout]
  exact hw

/-- The continuous self-map carried by one positive Artin monoid element. -/
def positiveArtinContinuousMap
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
    @ContinuousMap (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact ⟨positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a,
    positiveArtinConfigurationAction_continuous
      Q ρ hQ hArtin hComm hcont n a⟩

@[simp] theorem positiveArtinContinuousMap_apply
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
    (n : ℕ) (a : PositiveArtinMonoid) (p : Unordered Q n) :
    positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a p =
      positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p :=
  by
    letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    rfl

/-- Multiplication in the positive Artin monoid is realized by composition of
the corresponding continuous configuration maps. -/
theorem positiveArtinContinuousMap_mul
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
    positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n (a * b) =
      @ContinuousMap.comp (Unordered Q n) (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)
        (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a)
        (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n b) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply ContinuousMap.ext
  intro p
  exact congrFun
    (map_mul (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n) a b) p

end InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
