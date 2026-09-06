import InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
import InfoGeometry.Canonical.FiniteMajoranaBraiding

/-!
# Algebraic braid-word action on unordered projective-null configurations

This owner evaluates the repository's existing `BraidWord` carrier by the
already proved unordered configuration generators.  It proves only word
composition and the Yang--Baxter rewrite.  A word is not identified with a
loop, a fundamental-group element, a monodromy operator, or an anyon model.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

instance braidWordMonoid : Monoid BraidWord where
  one := []
  mul := List.append
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_assoc := List.append_assoc

/-- Evaluate a finite braid word by composing the descended configuration
generators, with the rightmost word letters acting first. -/
def mapUnorderedConfigurationWord
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ) :
    BraidWord → Unordered Q n → Unordered Q n
  | [], p => p
  | i :: w, p =>
      mapUnorderedConfiguration Q ρ hQ i n
        (mapUnorderedConfigurationWord Q ρ hQ n w p)

@[simp] theorem mapUnorderedConfigurationWord_nil
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ) (p : Unordered Q n) :
    mapUnorderedConfigurationWord Q ρ hQ n [] p = p :=
  rfl

@[simp] theorem mapUnorderedConfigurationWord_cons
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (i : ℕ) (w : BraidWord) (p : Unordered Q n) :
    mapUnorderedConfigurationWord Q ρ hQ n (i :: w) p =
      mapUnorderedConfiguration Q ρ hQ i n
        (mapUnorderedConfigurationWord Q ρ hQ n w p) :=
  rfl

theorem mapUnorderedConfigurationWord_append
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (u v : BraidWord) (p : Unordered Q n) :
    mapUnorderedConfigurationWord Q ρ hQ n (u ++ v) p =
      mapUnorderedConfigurationWord Q ρ hQ n u
        (mapUnorderedConfigurationWord Q ρ hQ n v p) := by
  induction u generalizing v p with
  | nil => rfl
  | cons i u ih =>
      simp only [List.cons_append, mapUnorderedConfigurationWord_cons]
      exact congrArg (mapUnorderedConfiguration Q ρ hQ i n) (ih v p)

/-- The word evaluation is a genuine monoid homomorphism into endofunctions
on the unordered configuration carrier. -/
def mapUnorderedConfigurationWordHom
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ) :
    BraidWord →* Function.End (Unordered Q n) where
  toFun w := mapUnorderedConfigurationWord Q ρ hQ n w
  map_one' := by
    funext p
    rfl
  map_mul' u v := by
    funext p
    exact mapUnorderedConfigurationWord_append Q ρ hQ n u v p

@[simp] theorem mapUnorderedConfigurationWordHom_apply
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (w : BraidWord) (p : Unordered Q n) :
    mapUnorderedConfigurationWordHom Q ρ hQ n w p =
      mapUnorderedConfigurationWord Q ρ hQ n w p :=
  rfl

theorem mapUnorderedConfigurationWord_braid_rewrite
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i : ℕ) (left right : BraidWord) (n : ℕ) (p : Unordered Q n) :
    mapUnorderedConfigurationWord Q ρ hQ n
        (left ++ [i, i + 1, i] ++ right) p =
      mapUnorderedConfigurationWord Q ρ hQ n
        (left ++ [i + 1, i, i + 1] ++ right) p := by
  rw [mapUnorderedConfigurationWord_append,
    mapUnorderedConfigurationWord_append,
    mapUnorderedConfigurationWord_append,
    mapUnorderedConfigurationWord_append]
  congr 1
  simp only [mapUnorderedConfigurationWord_cons,
    mapUnorderedConfigurationWord_nil]
  exact mapUnorderedConfiguration_artin_relation Q ρ hQ hArtin i n
    (mapUnorderedConfigurationWord Q ρ hQ n right p)

theorem mapUnorderedConfigurationWord_commute_rewrite
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (left right : BraidWord) (n : ℕ) (p : Unordered Q n) :
    mapUnorderedConfigurationWord Q ρ hQ n
        (left ++ [i, j] ++ right) p =
      mapUnorderedConfigurationWord Q ρ hQ n
        (left ++ [j, i] ++ right) p := by
  rw [mapUnorderedConfigurationWord_append,
    mapUnorderedConfigurationWord_append,
    mapUnorderedConfigurationWord_append,
    mapUnorderedConfigurationWord_append]
  congr 1
  simp only [mapUnorderedConfigurationWord_cons,
    mapUnorderedConfigurationWord_nil]
  exact mapUnorderedConfiguration_commute_relation Q ρ hQ i j n hComm
    (mapUnorderedConfigurationWord Q ρ hQ n right p)

theorem mapUnorderedConfigurationWordHom_braid_rewrite
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i : ℕ) (left right : BraidWord) (n : ℕ) :
    mapUnorderedConfigurationWordHom Q ρ hQ n
        (left ++ [i, i + 1, i] ++ right) =
      mapUnorderedConfigurationWordHom Q ρ hQ n
        (left ++ [i + 1, i, i + 1] ++ right) := by
  funext p
  exact mapUnorderedConfigurationWord_braid_rewrite Q ρ hQ hArtin i left right n p

theorem mapUnorderedConfigurationWordHom_commute_rewrite
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (left right : BraidWord) (n : ℕ) :
    mapUnorderedConfigurationWordHom Q ρ hQ n
        (left ++ [i, j] ++ right) =
      mapUnorderedConfigurationWordHom Q ρ hQ n
        (left ++ [j, i] ++ right) := by
  funext p
  exact mapUnorderedConfigurationWord_commute_rewrite Q ρ hQ i j hComm
    left right n p

end InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction
