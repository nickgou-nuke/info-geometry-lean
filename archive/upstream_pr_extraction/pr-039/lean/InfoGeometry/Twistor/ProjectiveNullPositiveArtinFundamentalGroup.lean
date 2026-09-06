import InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
import InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup

/-!
# Fundamental-group maps for positive Artin configuration actions

This owner applies Mathlib's `FundamentalGroup.map` to the continuous maps
induced by positive Artin elements.  The basepoint is allowed to move to its
image.  No fixed-basepoint identification, braid-group identification,
geometric exchange loop, or monodromy representation is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroup

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def positiveArtinFundamentalGroupMap
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
    let _ := unorderedConfigurationTopology Q n
    FundamentalGroup (Unordered Q n) p →*
      FundamentalGroup (Unordered Q n)
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact FundamentalGroup.map
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a) p

/-- The identity positive-Artin element induces the identity map on the
based fundamental group (the basepoint is fixed by the identity action). -/
theorem positiveArtinFundamentalGroupMap_one
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
    (n : ℕ) (p : Unordered Q n) :
    let _ := unorderedConfigurationTopology Q n
    positiveArtinFundamentalGroupMap Q ρ hQ hArtin hComm hcont n 1 p =
      MonoidHom.id (FundamentalGroup (Unordered Q n) p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold positiveArtinFundamentalGroupMap
  have hmap :
      positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n 1 =
        (@ContinuousMap.id (Unordered Q n)
          (unorderedConfigurationTopology Q n)) := by
    apply ContinuousMap.ext
    intro q
    change positiveArtinConfigurationAction Q ρ hQ hArtin hComm n 1 q = q
    rw [map_one]
    rfl
  cases hmap
  unfold FundamentalGroup.map
  apply MonoidHom.ext
  intro q
  change Path.Homotopic.Quotient.map q (ContinuousMap.id (Unordered Q n)) = q
  refine Quotient.inductionOn q ?_
  intro r
  rfl

theorem positiveArtinFundamentalGroupMap_mul
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
    (n : ℕ) (a b : PositiveArtinMonoid) (p : Unordered Q n) :
    let _ := unorderedConfigurationTopology Q n
    HEq (positiveArtinFundamentalGroupMap Q ρ hQ hArtin hComm hcont n (a * b) p)
      ((positiveArtinFundamentalGroupMap Q ρ hQ hArtin hComm hcont n a
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n b p)).comp
          (positiveArtinFundamentalGroupMap Q ρ hQ hArtin hComm hcont n b p)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold positiveArtinFundamentalGroupMap
  have hcomp := fundamentalGroup_map_comp
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a)
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n b) p
  have htransport := fundamentalGroup_map_heq_of_eq
    (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n (a * b))
    ((positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n a).comp
      (positiveArtinContinuousMap Q ρ hQ hArtin hComm hcont n b))
    (positiveArtinContinuousMap_mul Q ρ hQ hArtin hComm hcont n a b) p
  exact htransport.trans (heq_of_eq hcomp)

end InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroup
