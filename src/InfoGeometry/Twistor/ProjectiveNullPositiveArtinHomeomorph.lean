import InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Homeomorphism readout of the positive Artin action

The positive Artin monoid has no inverse generators, but each concrete
configuration generator is already a homeomorphism because it comes from a
linear equivalence and its inverse is continuous.  This owner transports that
fact through the native `PresentedMonoid.inductionOn` recursion.

It remains a global homeomorphism action on the configuration carrier.  No
exchange path, braid-group element, fixed-basepoint monodromy, or anyon claim
is introduced.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullPositiveArtinHomeomorph

open scoped LinearAlgebra.Projectivization

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinTopology
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem positiveArtinConfigurationAction_isHomeomorph
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
    @IsHomeomorph (Unordered Q n) (Unordered Q n)
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
  rw [hreadout]
  exact mapUnorderedConfigurationWord_isHomeomorph
    Q ρ hQ n hcont hcont_inv w.toList

def positiveArtinConfigurationActionHomeomorph
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
    Unordered Q n ≃ₜ Unordered Q n := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact (positiveArtinConfigurationAction_isHomeomorph
    Q ρ hQ hArtin hComm hcont hcont_inv n a).homeomorph _

/-- The identity element acts by the identity homeomorphism. -/
theorem positiveArtinConfigurationActionHomeomorph_one
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
    positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
        hcont hcont_inv n 1 = Homeomorph.refl (Unordered Q n) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply Homeomorph.ext
  intro p
  change positiveArtinConfigurationAction Q ρ hQ hArtin hComm n 1 p = p
  rw [map_one]
  rfl

@[simp] theorem positiveArtinConfigurationActionHomeomorph_apply
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
    positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
        hcont hcont_inv n a p =
      positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p := by
  rfl

theorem positiveArtinConfigurationActionHomeomorph_mul
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
    positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
        hcont hcont_inv n (a * b) =
      (positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
        hcont hcont_inv n b).trans
        (positiveArtinConfigurationActionHomeomorph Q ρ hQ hArtin hComm
          hcont hcont_inv n a) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply Homeomorph.ext
  intro p
  change positiveArtinConfigurationAction Q ρ hQ hArtin hComm n (a * b) p =
    positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a
      (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n b p)
  exact congrFun (map_mul (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n)
    a b) p

end InfoGeometry.Twistor.ProjectiveNullPositiveArtinHomeomorph
