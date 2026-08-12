import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup
import InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology

/-!
# Fundamental-groupoid transport of projective-null word actions

This owner consumes the continuous word maps on unordered null
configurations through Mathlib's fundamental groupoid functor.  The
groupoid keeps the image object (and hence the basepoint) explicit, so
composition is expressed by the native functorial `map_comp` theorem rather
than by an artificial equality between based fundamental groups.

The Artin and far-commutativity results below are still algebraic rewrites of
the already constructed word action.  No identification with a braid group,
no choice of a fixed basepoint, and no monodromy or anyon claim is made.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroupoid

open CategoryTheory
open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def fundamentalGroupoidWordMap
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (w : BraidWord) :
    let _ := unorderedConfigurationTopology Q n
    CategoryTheory.Functor
      (FundamentalGroupoid (Unordered Q n))
      (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  exact FundamentalGroupoid.map (wordContinuousMap Q ρ hQ n hcont w)

/- The empty word induces the identity functor on the fundamental groupoid. -/
theorem fundamentalGroupoidWordMap_nil
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) :
    let _ := unorderedConfigurationTopology Q n
    fundamentalGroupoidWordMap Q ρ hQ n hcont [] =
      𝟭 (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  unfold fundamentalGroupoidWordMap
  have hmap :
      wordContinuousMap Q ρ hQ n hcont [] =
        (@ContinuousMap.id (Unordered Q n)
          (unorderedConfigurationTopology Q n)) := by
    apply ContinuousMap.ext
    intro q
    rfl
  cases hmap
  exact FundamentalGroupoid.map_id

theorem fundamentalGroupoidWordMap_append
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (u v : BraidWord) :
    let _ := unorderedConfigurationTopology Q n
    fundamentalGroupoidWordMap Q ρ hQ n hcont (u ++ v) =
      (fundamentalGroupoidWordMap Q ρ hQ n hcont v).comp
        (fundamentalGroupoidWordMap Q ρ hQ n hcont u) := by
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  unfold fundamentalGroupoidWordMap
  rw [wordContinuousMap_append Q ρ hQ n hcont u v]
  exact FundamentalGroupoid.map_comp _ _

theorem fundamentalGroupoidWordMap_eq_of_continuousMap_eq
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    {u v : BraidWord}
    (h : wordContinuousMap Q ρ hQ n hcont u =
      wordContinuousMap Q ρ hQ n hcont v) :
    let _ := unorderedConfigurationTopology Q n
    fundamentalGroupoidWordMap Q ρ hQ n hcont u =
      fundamentalGroupoidWordMap Q ρ hQ n hcont v := by
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  exact congrArg FundamentalGroupoid.map h

theorem fundamentalGroupoidWordMap_braid_rewrite
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i : ℕ) (left right : BraidWord) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q n
    fundamentalGroupoidWordMap Q ρ hQ n hcont
        (left ++ [i, i + 1, i] ++ right) =
      fundamentalGroupoidWordMap Q ρ hQ n hcont
        (left ++ [i + 1, i, i + 1] ++ right) := by
  apply fundamentalGroupoidWordMap_eq_of_continuousMap_eq
  exact wordContinuousMap_braid_rewrite Q ρ hQ hcont hArtin i left right n

theorem fundamentalGroupoidWordMap_commute_rewrite
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (left right : BraidWord) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q n
    fundamentalGroupoidWordMap Q ρ hQ n hcont
        (left ++ [i, j] ++ right) =
      fundamentalGroupoidWordMap Q ρ hQ n hcont
        (left ++ [j, i] ++ right) := by
  apply fundamentalGroupoidWordMap_eq_of_continuousMap_eq
  exact wordContinuousMap_commute_rewrite Q ρ hQ hcont i j hComm left right n

end InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroupoid
