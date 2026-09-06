import InfoGeometry.Twistor.ProjectiveNullConfiguration

/-!
# Unordered configurations on a projective null boundary

This owner forms the finite quotient of ordered null configurations by
reindexing with `Equiv.Perm (Fin n)`.  It provides only the algebraic orbit
carrier and descent of the already proved diagonal projective action.  No
topology, fundamental group, spherical braid group, or monodromy is claimed.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullArtinBraid

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev Ordered (Q : QuadraticForm K V) (n : ℕ) :=
  NullOrderedConfiguration Q n

def permute (Q : QuadraticForm K V) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : Ordered Q n) : Ordered Q n := by
  refine ⟨fun j => p.1 (σ j), ?_⟩
  intro i j hij heq
  apply p.2 (σ i) (σ j) (by
    intro h
    apply hij
    exact σ.injective h)
  exact heq

@[simp] theorem permute_apply (Q : QuadraticForm K V) (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (p : Ordered Q n) (j : Fin n) :
    (permute Q n σ p).1 j = p.1 (σ j) := rfl

/-- The reindexing action on an ordered distinct configuration is free. -/
theorem permute_eq_self_imp_eq_refl (Q : QuadraticForm K V) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (p : Ordered Q n) :
    permute Q n σ p = p → σ = Equiv.refl _ := by
  intro h
  apply Equiv.ext
  intro j
  by_contra hj
  have hj' : j ≠ σ j := by
    intro hji
    apply hj
    exact hji.symm
  apply p.2 j (σ j) hj'
  exact (congrArg (fun q : Ordered Q n => q.1 j) h).symm

@[simp] theorem permute_refl (Q : QuadraticForm K V) (n : ℕ)
    (p : Ordered Q n) :
    permute Q n (Equiv.refl _) p = p := by
  apply Subtype.ext
  funext j
  rfl

theorem permute_comp (Q : QuadraticForm K V) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) (p : Ordered Q n) :
    permute Q n σ (permute Q n τ p) =
      permute Q n (σ.trans τ) p := by
  apply Subtype.ext
  funext j
  change p.1 (τ (σ j)) = p.1 ((σ.trans τ) j)
  rfl

theorem permute_injective (Q : QuadraticForm K V) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permute Q n σ) := by
  intro p q h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun c : Ordered Q n => c.1 (σ.symm j)) h
  simpa [permute] using hj

theorem permute_eq_of_eq (Q : QuadraticForm K V) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) (p : Ordered Q n)
    (h : permute Q n σ p = permute Q n τ p) :
    σ = τ := by
  apply Equiv.ext
  intro j
  by_contra hj
  have hpoint : p.1 (σ j) = p.1 (τ j) := by
    exact congrArg (fun c : Ordered Q n => c.1 j) h
  have hne : σ j ≠ τ j := by
    intro hst
    exact hj hst
  exact (p.2 (σ j) (τ j) hne) hpoint

def reindexSetoid (Q : QuadraticForm K V) (n : ℕ) : Setoid (Ordered Q n) where
  r p q := ∃ σ : Equiv.Perm (Fin n), q = permute Q n σ p
  iseqv := by
    constructor
    · intro p
      exact ⟨Equiv.refl _, by apply Subtype.ext; funext j; rfl⟩
    · intro p q h
      obtain ⟨σ, hσ⟩ := h
      refine ⟨σ.symm, ?_⟩
      apply Subtype.ext
      funext j
      rw [hσ]
      simp [permute]
    · intro p q r hpq hqr
      obtain ⟨σ, hσ⟩ := hpq
      obtain ⟨τ, hτ⟩ := hqr
      refine ⟨τ.trans σ, ?_⟩
      apply Subtype.ext
      funext j
      rw [hτ, hσ]
      simp [permute]

abbrev Unordered (Q : QuadraticForm K V) (n : ℕ) :=
  Quotient (reindexSetoid Q n)

instance reindexSetoidInstance (Q : QuadraticForm K V) (n : ℕ) :
    Setoid (Ordered Q n) :=
  reindexSetoid Q n

theorem mapOrderedConfiguration_respects_reindex
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ)
    (σ : Equiv.Perm (Fin n)) (p : Ordered Q n) :
    mapOrderedConfiguration Q ρ hQ generator n (permute Q n σ p) =
      permute Q n σ (mapOrderedConfiguration Q ρ hQ generator n p) := by
  apply Subtype.ext
  funext j
  rfl

theorem mapOrderedConfiguration_artin_relation
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i n : ℕ) (p : Ordered Q n) :
    mapOrderedConfiguration Q ρ hQ i n
        (mapOrderedConfiguration Q ρ hQ (i + 1) n
          (mapOrderedConfiguration Q ρ hQ i n p)) =
      mapOrderedConfiguration Q ρ hQ (i + 1) n
        (mapOrderedConfiguration Q ρ hQ i n
          (mapOrderedConfiguration Q ρ hQ (i + 1) n p)) := by
  apply Subtype.ext
  funext j
  change
    nullProjectiveGenerator Q ρ hQ i
        (nullProjectiveGenerator Q ρ hQ (i + 1)
          (nullProjectiveGenerator Q ρ hQ i (p.1 j))) =
      nullProjectiveGenerator Q ρ hQ (i + 1)
        (nullProjectiveGenerator Q ρ hQ i
          (nullProjectiveGenerator Q ρ hQ (i + 1) (p.1 j)))
  exact nullProjectiveGenerator_artin_relation Q ρ hQ hArtin i (p.1 j)

theorem mapOrderedConfiguration_commute_relation
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (i j n : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (p : Ordered Q n) :
    mapOrderedConfiguration Q ρ hQ i n
        (mapOrderedConfiguration Q ρ hQ j n p) =
      mapOrderedConfiguration Q ρ hQ j n
        (mapOrderedConfiguration Q ρ hQ i n p) := by
  apply Subtype.ext
  funext k
  change
    nullProjectiveGenerator Q ρ hQ i
        (nullProjectiveGenerator Q ρ hQ j (p.1 k)) =
      nullProjectiveGenerator Q ρ hQ j
        (nullProjectiveGenerator Q ρ hQ i (p.1 k))
  exact nullProjectiveGenerator_commute_relation Q ρ hQ i j hComm (p.1 k)

def mapUnorderedConfiguration
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ) :
    Unordered Q n → Unordered Q n :=
  Quotient.lift
    (fun p => Quotient.mk' (mapOrderedConfiguration Q ρ hQ generator n p))
    (by
      intro p q hpq
      obtain ⟨σ, hσ⟩ := hpq
      apply Quotient.sound
      refine ⟨σ, ?_⟩
      rw [hσ, mapOrderedConfiguration_respects_reindex])

theorem mapUnorderedConfiguration_mk
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ)
    (p : Ordered Q n) :
    mapUnorderedConfiguration Q ρ hQ generator n (Quotient.mk' p) =
      Quotient.mk' (mapOrderedConfiguration Q ρ hQ generator n p) :=
  rfl

theorem mapUnorderedConfiguration_artin_relation
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i n : ℕ) (p : Unordered Q n) :
    mapUnorderedConfiguration Q ρ hQ i n
        (mapUnorderedConfiguration Q ρ hQ (i + 1) n
          (mapUnorderedConfiguration Q ρ hQ i n p)) =
      mapUnorderedConfiguration Q ρ hQ (i + 1) n
        (mapUnorderedConfiguration Q ρ hQ i n
          (mapUnorderedConfiguration Q ρ hQ (i + 1) n p)) := by
  refine Quotient.inductionOn p ?_
  intro c
  change Quotient.mk'
      (mapOrderedConfiguration Q ρ hQ i n
        (mapOrderedConfiguration Q ρ hQ (i + 1) n
          (mapOrderedConfiguration Q ρ hQ i n c))) =
    Quotient.mk'
      (mapOrderedConfiguration Q ρ hQ (i + 1) n
        (mapOrderedConfiguration Q ρ hQ i n
          (mapOrderedConfiguration Q ρ hQ (i + 1) n c)))
  exact congrArg Quotient.mk'
    (mapOrderedConfiguration_artin_relation Q ρ hQ hArtin i n c)

theorem mapUnorderedConfiguration_commute_relation
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (i j n : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (p : Unordered Q n) :
    mapUnorderedConfiguration Q ρ hQ i n
        (mapUnorderedConfiguration Q ρ hQ j n p) =
      mapUnorderedConfiguration Q ρ hQ j n
        (mapUnorderedConfiguration Q ρ hQ i n p) := by
  refine Quotient.inductionOn p ?_
  intro c
  change Quotient.mk'
      (mapOrderedConfiguration Q ρ hQ i n
        (mapOrderedConfiguration Q ρ hQ j n c)) =
    Quotient.mk'
      (mapOrderedConfiguration Q ρ hQ j n
        (mapOrderedConfiguration Q ρ hQ i n c))
  exact congrArg Quotient.mk'
    (mapOrderedConfiguration_commute_relation Q ρ hQ i j n hComm c)

theorem mapUnorderedConfiguration_injective
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ) :
    Function.Injective (mapUnorderedConfiguration Q ρ hQ generator n) := by
  intro p q hpq
  revert hpq
  refine Quotient.inductionOn₂ p q ?_
  intro p q hpq
  change Quotient.mk' (mapOrderedConfiguration Q ρ hQ generator n p) =
    Quotient.mk' (mapOrderedConfiguration Q ρ hQ generator n q) at hpq
  obtain ⟨σ, hσ⟩ := Quotient.exact hpq
  apply Quotient.sound
  refine ⟨σ, ?_⟩
  apply mapOrderedConfiguration_injective Q ρ hQ generator n
  apply Subtype.ext
  funext j
  calc
    (mapOrderedConfiguration Q ρ hQ generator n q).1 j =
        (permute Q n σ (mapOrderedConfiguration Q ρ hQ generator n p)).1 j :=
      congrFun (congrArg Subtype.val hσ) j
    _ = (mapOrderedConfiguration Q ρ hQ generator n (permute Q n σ p)).1 j := by
      rw [mapOrderedConfiguration_respects_reindex]

end InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
