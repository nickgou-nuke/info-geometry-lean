import InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Fundamental-group maps induced by projective-null word actions

This owner consumes Mathlib's `FundamentalGroup.map` for the continuous word
actions already constructed on unordered null configurations.  The basepoint
is allowed to move to its image.  No identification with an Artin braid
group, no fixed-basepoint monodromy, and no anyon interpretation is claimed.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup

open scoped LinearAlgebra.Projectivization

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Equality of continuous maps gives heterogeneous equality of their induced
fundamental-group maps.  Heterogeneous equality is the honest statement here:
the codomain fundamental groups are based at the two image points. -/
theorem fundamentalGroup_map_heq_of_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (h : f = g) (p : X) :
    HEq (FundamentalGroup.map f p) (FundamentalGroup.map g p) := by
  cases h
  rfl

/-- Functoriality of Mathlib's fundamental-group map for continuous-map
composition.  The statement is basepoint-aware: the intermediate basepoint
is `g x`, and no fixed-basepoint identification is inserted. -/
theorem fundamentalGroup_map_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) (g : C(X, Y)) (x : X) :
    FundamentalGroup.map (f.comp g) x =
      (FundamentalGroup.map f (g x)).comp (FundamentalGroup.map g x) := by
  unfold FundamentalGroup.map
  apply MonoidHom.ext
  intro q
  change Path.Homotopic.Quotient.map q (f.comp g) =
    Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.map q g) f
  refine Quotient.inductionOn q ?_
  intro r
  rfl

/-- The continuous map underlying one algebraic projective-null word action. -/
def wordContinuousMap
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (w : BraidWord) :
    @ContinuousMap (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n) (unorderedConfigurationTopology Q n) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact ContinuousMap.mk
    (mapUnorderedConfigurationWord Q ρ hQ n w)
    (mapUnorderedConfigurationWord_continuous Q ρ hQ n hcont w)

@[simp] theorem wordContinuousMap_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (w : BraidWord)
    (p : Unordered Q n) :
    wordContinuousMap Q ρ hQ n hcont w p =
      mapUnorderedConfigurationWord Q ρ hQ n w p :=
  rfl

/-- Mathlib's induced fundamental-group homomorphism, with the basepoint
sent along the word action. -/
def fundamentalGroupWordMap
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (w : BraidWord)
    (p : Unordered Q n) :
    @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p →*
    @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (wordContinuousMap Q ρ hQ n hcont w p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact FundamentalGroup.map (wordContinuousMap Q ρ hQ n hcont w) p

/- The empty word induces the identity on the based fundamental group. -/
theorem fundamentalGroupWordMap_nil_heq
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (p : Unordered Q n) :
    let _ := unorderedConfigurationTopology Q n
    HEq (fundamentalGroupWordMap Q ρ hQ n hcont [] p)
      (MonoidHom.id (FundamentalGroup (Unordered Q n) p)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  have hmap :
      wordContinuousMap Q ρ hQ n hcont [] =
        (@ContinuousMap.id (Unordered Q n)
          (unorderedConfigurationTopology Q n)) := by
    apply ContinuousMap.ext
    intro q
    rfl
  have hmap' :
      fundamentalGroupWordMap Q ρ hQ n hcont [] p =
        FundamentalGroup.map
        (@ContinuousMap.id (Unordered Q n)
            (unorderedConfigurationTopology Q n)) p := by
    unfold fundamentalGroupWordMap
    cases hmap
    rfl
  have hid :
      FundamentalGroup.map
          (@ContinuousMap.id (Unordered Q n)
            (unorderedConfigurationTopology Q n)) p =
        MonoidHom.id (FundamentalGroup (Unordered Q n) p) := by
    unfold FundamentalGroup.map
    apply MonoidHom.ext
    intro q
    change Path.Homotopic.Quotient.map q (ContinuousMap.id (Unordered Q n)) = q
    refine Quotient.inductionOn q ?_
    intro r
    rfl
  exact heq_of_eq (hmap'.trans hid)

/-! A fixed point turns the naturally moving-basepoint map above into an
ordinary endomorphism of one based fundamental group.  This is only a
basepoint transport theorem; it does not identify the map with braid
monodromy. -/

def fundamentalGroupWordMap_fixed_basepoint
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (w : BraidWord)
    (p : Unordered Q n)
    (hfix : mapUnorderedConfigurationWord Q ρ hQ n w p = p) :
    @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p →*
    @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  have hmap : wordContinuousMap Q ρ hQ n hcont w p = p := by
    simpa only [wordContinuousMap_apply] using hfix
  exact cast
    (congrArg
      (fun q =>
        @FundamentalGroup (Unordered Q n)
          (unorderedConfigurationTopology Q n) p →*
        @FundamentalGroup (Unordered Q n)
          (unorderedConfigurationTopology Q n) q)
      hmap)
    (fundamentalGroupWordMap Q ρ hQ n hcont w p)

theorem wordContinuousMap_append
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (u v : BraidWord) :
    wordContinuousMap Q ρ hQ n hcont (u ++ v) =
      @ContinuousMap.comp (Unordered Q n) (Unordered Q n) (Unordered Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)
        (unorderedConfigurationTopology Q n)
        (wordContinuousMap Q ρ hQ n hcont u)
        (wordContinuousMap Q ρ hQ n hcont v) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply ContinuousMap.ext
  intro p
  exact mapUnorderedConfigurationWord_append Q ρ hQ n u v p

theorem fundamentalGroupWordMap_append_heq
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (u v : BraidWord) (p : Unordered Q n) :
    HEq
      (fundamentalGroupWordMap Q ρ hQ n hcont (u ++ v) p)
      ((fundamentalGroupWordMap Q ρ hQ n hcont u
          (mapUnorderedConfigurationWord Q ρ hQ n v p)).comp
        (fundamentalGroupWordMap Q ρ hQ n hcont v p)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let fu := wordContinuousMap Q ρ hQ n hcont u
  let fv := wordContinuousMap Q ρ hQ n hcont v
  let fuv := wordContinuousMap Q ρ hQ n hcont (u ++ v)
  have hmaps : HEq (FundamentalGroup.map fuv p)
      (FundamentalGroup.map (fu.comp fv) p) :=
    fundamentalGroup_map_heq_of_eq fuv (fu.comp fv)
      (wordContinuousMap_append Q ρ hQ n hcont u v) p
  have hcomp := fundamentalGroup_map_comp fu fv p
  unfold fundamentalGroupWordMap
  exact hmaps.trans (heq_of_eq (by
    simpa only [fu, fv, wordContinuousMap_apply] using hcomp))

theorem wordContinuousMap_braid_rewrite
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
    wordContinuousMap Q ρ hQ n hcont
        (left ++ [i, i + 1, i] ++ right) =
      wordContinuousMap Q ρ hQ n hcont
        (left ++ [i + 1, i, i + 1] ++ right) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply ContinuousMap.ext
  intro p
  exact mapUnorderedConfigurationWord_braid_rewrite Q ρ hQ hArtin i left right n p

theorem wordContinuousMap_commute_rewrite
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (left right : BraidWord) (n : ℕ) :
    wordContinuousMap Q ρ hQ n hcont
        (left ++ [i, j] ++ right) =
      wordContinuousMap Q ρ hQ n hcont
        (left ++ [j, i] ++ right) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply ContinuousMap.ext
  intro p
  exact mapUnorderedConfigurationWord_commute_rewrite Q ρ hQ i j hComm
    left right n p

/-- The adjacent Artin rewrite induces the same fundamental-group map, with
the naturally moving image basepoint.  This is functorial transport through
`FundamentalGroup.map`, not a braid-group or monodromy identification. -/
theorem fundamentalGroupWordMap_braid_rewrite
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i : ℕ) (left right : BraidWord) (n : ℕ) (p : Unordered Q n) :
    HEq (fundamentalGroupWordMap Q ρ hQ n hcont
        (left ++ [i, i + 1, i] ++ right) p)
      (fundamentalGroupWordMap Q ρ hQ n hcont
        (left ++ [i + 1, i, i + 1] ++ right) p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact fundamentalGroup_map_heq_of_eq _ _
    (wordContinuousMap_braid_rewrite Q ρ hQ hcont hArtin i left right n) p

/-- A proved far-commutativity rewrite likewise induces the same
fundamental-group map with its natural image basepoint. -/
theorem fundamentalGroupWordMap_commute_rewrite
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (left right : BraidWord) (n : ℕ) (p : Unordered Q n) :
    HEq (fundamentalGroupWordMap Q ρ hQ n hcont
        (left ++ [i, j] ++ right) p)
      (fundamentalGroupWordMap Q ρ hQ n hcont
        (left ++ [j, i] ++ right) p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact fundamentalGroup_map_heq_of_eq _ _
    (wordContinuousMap_commute_rewrite Q ρ hQ hcont i j hComm left right n) p

end InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup
