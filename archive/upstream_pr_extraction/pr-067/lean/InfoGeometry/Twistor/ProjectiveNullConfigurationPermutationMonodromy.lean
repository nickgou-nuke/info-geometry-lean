import InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
import InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv

/-!
# Symmetric-group monodromy of projective-null configurations

Mathlib's categorical multiplication convention makes the direct deck
permutation readout anti-multiplicative.  Taking the inverse permutation gives
an honest representation of the based fundamental group in `S_n`.  Under the
already proved concrete equivalence between the covering fiber and `S_n`, this
representation acts by left multiplication.

This is finite covering-space monodromy.  It does not identify the source with
an Artin or spherical braid group and does not assert conformal-block or anyon
monodromy.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The ordinary symmetric-group representation obtained by inverting the
native anti-multiplicative endpoint permutation. -/
noncomputable def unorderedCoveringPermutationMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p) →*
      Equiv.Perm (Fin n) where
  toFun gamma :=
    (unorderedCoveringDeckPermutation Q n hLC hT2 p gamma).symm
  map_one' := by
    rw [unorderedCoveringDeckPermutation_one]
    rfl
  map_mul' gamma delta := by
    rw [unorderedCoveringDeckPermutation_mul]
    rfl

@[simp] theorem unorderedCoveringPermutationMonodromy_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma =
      (unorderedCoveringDeckPermutation Q n hLC hT2 p gamma).symm :=
  rfl

/-- Under the concrete equivalence between the covering fiber and `S_n`,
covering monodromy is left multiplication by the normalized deck
permutation. -/
theorem unorderedConfigurationFiberMonodromy_orderedFiberEquivPerm
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (tau : Equiv.Perm (Fin n)) :
    unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma
        (orderedFiberEquivPerm Q n p tau) =
      orderedFiberEquivPerm Q n p
        (unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma * tau) := by
  let base : {q : Ordered Q n //
      Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} := ⟨p, rfl⟩
  have hq : orderedFiberEquivPerm Q n p tau =
      unorderedConfigurationFiberDeckAction Q n p tau.symm base := by
    apply Subtype.ext
    rfl
  rw [hq, unorderedConfigurationFiberMonodromy_deck_equivariant]
  apply Subtype.ext
  change tau.symm • unorderedCoveringMonodromyEndpoint Q n hLC hT2 p gamma =
    permute Q n
      ((unorderedCoveringDeckPermutation Q n hLC hT2 p gamma).symm * tau) p
  rw [← unorderedCoveringDeckPermutation_smul Q n hLC hT2 p gamma]
  rw [← mul_smul]
  rfl

/-! ## Fiber labels -/

/-- Transport the covering-fiber monodromy to the canonical deck-group labels
of the ordered fiber.  The target is the permutation group of the finite set
`Equiv.Perm (Fin n)`; the opposite-valued deck readout remains available in
the lower-level deck-monodromy owner. -/
noncomputable def unorderedConfigurationDeckLabelMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p) →*
      Equiv.Perm (Equiv.Perm (Fin n)) where
  toFun gamma :=
    let e := orderedFiberEquivPerm Q n p
    e.trans ((unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma).trans e.symm)
  map_one' := by
    apply Equiv.ext
    intro σ
    let e := orderedFiberEquivPerm Q n p
    change e.symm
        (unorderedConfigurationFiberMonodromy Q n hLC hT2 p 1 (e σ)) = σ
    rw [map_one]
    exact e.symm_apply_apply σ
  map_mul' gamma delta := by
    apply Equiv.ext
    intro σ
    dsimp
    rw [map_mul]
    rw [Equiv.Perm.mul_apply]
    simp only [Equiv.apply_symm_apply]

theorem unorderedConfigurationDeckLabelMonodromy_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (σ : Equiv.Perm (Fin n)) :
    unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p gamma σ =
      unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma * σ := by
  dsimp [unorderedConfigurationDeckLabelMonodromy]
  let e := orderedFiberEquivPerm Q n p
  change e.symm
      (unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma (e σ)) = _
  rw [unorderedConfigurationFiberMonodromy_orderedFiberEquivPerm]
  exact e.symm_apply_apply _

@[simp] theorem unorderedConfigurationDeckLabelMonodromy_apply_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p gamma 1 =
      unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma := by
  rw [unorderedConfigurationDeckLabelMonodromy_apply]
  simp

theorem unorderedConfigurationDeckLabelMonodromy_eq_one_iff
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p gamma = 1 ↔
      unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma = 1 := by
  constructor
  · intro h
    simpa using congrArg (fun f => f 1) h
  · intro h
    apply Equiv.ext
    intro σ
    rw [unorderedConfigurationDeckLabelMonodromy_apply, h]
    simp

theorem unorderedConfigurationDeckLabelMonodromy_eq_iff
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma delta : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p gamma =
        unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p delta ↔
      unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma =
        unorderedCoveringPermutationMonodromy Q n hLC hT2 p delta := by
  constructor
  · intro h
    simpa using congrArg (fun f => f 1) h
  · intro h
    apply Equiv.ext
    intro σ
    rw [unorderedConfigurationDeckLabelMonodromy_apply,
      unorderedConfigurationDeckLabelMonodromy_apply, h]

@[simp] theorem unorderedConfigurationDeckLabelMonodromy_mul_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma delta : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (σ : Equiv.Perm (Fin n)) :
    unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p (gamma * delta) σ =
      unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p gamma
        (unorderedConfigurationDeckLabelMonodromy Q n hLC hT2 p delta σ) := by
  rw [map_mul]
  rfl

end InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
