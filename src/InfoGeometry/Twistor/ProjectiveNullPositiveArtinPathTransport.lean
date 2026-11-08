import InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Path transport for positive Artin configuration actions

Each positive Artin element induces a continuous map on unordered
projective-null configurations.  This owner applies Mathlib's native
`Path.map` and records its compatibility with path concatenation.  It does
not select exchange paths, identify a braid group, or construct monodromy.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullPositiveArtinPathTransport

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def positiveArtinPathTransport
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
    (n : ℕ) (a : PositiveArtinMonoid)
    {p q : Unordered Q n}
    (γ : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p q) :
    @Path (Unordered Q n) (unorderedConfigurationTopology Q n)
      (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p)
      (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a q) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact γ.map (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a).continuous

/-- Transport sends the constant path to the constant path at the image
configuration. -/
theorem positiveArtinPathTransport_refl
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
    (n : ℕ) (a : PositiveArtinMonoid)
    (p : Unordered Q n) :
    positiveArtinPathTransport Q ρ hQ hArtin hComm hcont n a
        (@Path.refl (Unordered Q n) (unorderedConfigurationTopology Q n) p) =
      @Path.refl (Unordered Q n) (unorderedConfigurationTopology Q n)
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  change (@Path.refl (Unordered Q n) (unorderedConfigurationTopology Q n) p).map
      (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a).continuous = _
  rfl

theorem positiveArtinPathTransport_trans
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
    (n : ℕ) (a : PositiveArtinMonoid)
    {p q r : Unordered Q n}
    (γ : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p q)
    (δ : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) q r) :
    positiveArtinPathTransport Q ρ hQ hArtin hComm hcont n a
        (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
          p q r γ δ) =
      @Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p)
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a q)
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a r)
        (positiveArtinPathTransport Q ρ hQ hArtin hComm hcont n a γ)
        (positiveArtinPathTransport Q ρ hQ hArtin hComm hcont n a δ) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact Path.map_trans γ δ
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a).continuous

theorem positiveArtinPathTransport_homotopic
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
    (n : ℕ) (a : PositiveArtinMonoid)
    {p q : Unordered Q n}
    {γ δ : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p q}
    (hγδ : @Path.Homotopic (Unordered Q n) (unorderedConfigurationTopology Q n)
      p q γ δ) :
    @Path.Homotopic (Unordered Q n) (unorderedConfigurationTopology Q n)
      (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p)
      (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a q)
      (positiveArtinPathTransport Q ρ hQ hArtin hComm hcont n a γ)
      (positiveArtinPathTransport Q ρ hQ hArtin hComm hcont n a δ) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact hγδ.map
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a)

end InfoGeometry.Twistor.ProjectiveNullPositiveArtinPathTransport
