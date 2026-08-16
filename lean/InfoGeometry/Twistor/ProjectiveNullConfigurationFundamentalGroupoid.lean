import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
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
open scoped LinearAlgebra.Projectivization
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

/-! A finite word whose generators and inverses are continuous induces an
equivalence of fundamental groupoids.  The equivalence is obtained from the
native `Homeomorph.toHomotopyEquiv` and Mathlib's
`FundamentalGroupoidFunctor.equivOfHomotopyEquiv`; no basepoint or braid-group
identification is introduced here. -/
noncomputable def fundamentalGroupoidWordMap_equivalence
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V))) (w : BraidWord) :
    let _ := unorderedConfigurationTopology Q n
    FundamentalGroupoid (Unordered Q n) ≌
      FundamentalGroupoid (Unordered Q n) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  let hhomeo : IsHomeomorph
      (mapUnorderedConfigurationWord Q ρ hQ n w) :=
    mapUnorderedConfigurationWord_isHomeomorph Q ρ hQ n hcont hcont_inv w
  let e : (Unordered Q n) ≃ₜ (Unordered Q n) := hhomeo.homeomorph _
  exact FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv

/-- The forward functor of the groupoid equivalence is the native word map. -/
theorem fundamentalGroupoidWordMap_equivalence_functor
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V))) (w : BraidWord) :
    let _ := unorderedConfigurationTopology Q n
    (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv w).functor =
      fundamentalGroupoidWordMap Q ρ hQ n hcont w := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  let hhomeo : IsHomeomorph
      (mapUnorderedConfigurationWord Q ρ hQ n w) :=
    mapUnorderedConfigurationWord_isHomeomorph Q ρ hQ n hcont hcont_inv w
  let e : (Unordered Q n) ≃ₜ (Unordered Q n) := hhomeo.homeomorph _
  unfold fundamentalGroupoidWordMap_equivalence
  change FundamentalGroupoid.map
      (e : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)) =
    FundamentalGroupoid.map
      (wordContinuousMap Q ρ hQ n hcont w)
  congr 1

/-- A word action which is already known to be a homeomorphism induces an
    equivalence of fundamental groupoids.  This is the native homotopy
    transport statement; it does not choose a basepoint or identify the
    resulting groupoids with a braid group. -/
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

/-- The empty word gives the identity functor under the groupoid equivalence. -/
theorem fundamentalGroupoidWordMap_equivalence_functor_nil
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V))) :
    let _ := unorderedConfigurationTopology Q n
    (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv []).functor =
      𝟭 (FundamentalGroupoid (Unordered Q n)) := by
  rw [fundamentalGroupoidWordMap_equivalence_functor,
    fundamentalGroupoidWordMap_nil]

/- The inverse of the empty-word equivalence is the identity functor as well.
This is the inverse-side companion to the forward identity theorem above. -/
theorem fundamentalGroupoidWordMap_equivalence_inverse_nil
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V))) :
    let _ := unorderedConfigurationTopology Q n
    (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv []).inverse =
      𝟭 (FundamentalGroupoid (Unordered Q n)) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  let hhomeo : IsHomeomorph
      (mapUnorderedConfigurationWord Q ρ hQ n []) :=
    mapUnorderedConfigurationWord_isHomeomorph Q ρ hQ n hcont hcont_inv []
  let e : (Unordered Q n) ≃ₜ (Unordered Q n) := hhomeo.homeomorph _
  unfold fundamentalGroupoidWordMap_equivalence
  change FundamentalGroupoid.map
      (e.symm : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)) =
    𝟭 (FundamentalGroupoid (Unordered Q n))
  have he : e = Homeomorph.refl (Unordered Q n) := by
    apply Homeomorph.ext
    intro p
    rfl
  rw [he]
  exact FundamentalGroupoid.map_id

/- The inverse component is the groupoid map of the inverse homeomorphism.
This exposes the concrete inverse without choosing a basepoint or introducing
an identification with a braid group. -/
theorem fundamentalGroupoidWordMap_equivalence_inverse
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V))) (w : BraidWord) :
    let _ := unorderedConfigurationTopology Q n
    (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv w).inverse =
      FundamentalGroupoid.map
        ((mapUnorderedConfigurationWord_isHomeomorph Q ρ hQ n hcont hcont_inv w).homeomorph _).symm := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) :=
    unorderedConfigurationTopology Q n
  let hhomeo : IsHomeomorph
      (mapUnorderedConfigurationWord Q ρ hQ n w) :=
    mapUnorderedConfigurationWord_isHomeomorph Q ρ hQ n hcont hcont_inv w
  let e : (Unordered Q n) ≃ₜ (Unordered Q n) := hhomeo.homeomorph _
  unfold fundamentalGroupoidWordMap_equivalence
  change FundamentalGroupoid.map
      (e.symm : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)) =
    FundamentalGroupoid.map
      (e.symm : @ContinuousMap (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n))
  rfl

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

/-- Append composition is preserved by the forward functors of the
    corresponding groupoid equivalences. -/
theorem fundamentalGroupoidWordMap_equivalence_functor_append
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (u v : BraidWord) :
    let _ := unorderedConfigurationTopology Q n
    (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv (u ++ v)).functor =
      (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv v).functor.comp
        (fundamentalGroupoidWordMap_equivalence Q ρ hQ n hcont hcont_inv u).functor := by
  rw [fundamentalGroupoidWordMap_equivalence_functor,
    fundamentalGroupoidWordMap_equivalence_functor,
    fundamentalGroupoidWordMap_equivalence_functor,
    fundamentalGroupoidWordMap_append]

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
