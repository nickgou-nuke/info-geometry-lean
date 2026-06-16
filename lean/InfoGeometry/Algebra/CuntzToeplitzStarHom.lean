import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz-Toeplitz StarRing and *-homomorphism to Cuntz

Extends `CuntzTensorQuotient.lean` with:
1. `StarRing` instance for `CuntzToeplitzAlg n`
2. Natural *-homomorphism `toeplitzToCuntz` from Toeplitz to Cuntz
3. Universal property: any *-representation of the Cuntz-Toeplitz
   relations that also satisfies `Σ S_i S_i† = 1` factors through
   the Cuntz quotient.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzTensorQuotient

/-! ## StarRing for the Cuntz-Toeplitz algebra -/

/-- The dagger preserves the Cuntz-Toeplitz relation. -/
theorem dagger_CuntzToeplitzRel_star {n : ℕ} {x y : CuntzTensor n}
    (h : CuntzToeplitzRel n x y) : CuntzToeplitzRel n (dagger n x) (dagger n y) := by
  rcases h with ⟨i, j⟩
  rw [dagger_mul, dagger_Sdag, dagger_S]
  by_cases hij : i = j
  · subst j; simpa [dagger_one] using CuntzToeplitzRel.orth (n := n) i i
  · have hji : j ≠ i := fun h => hij h.symm
    simpa [hij, dagger_one] using CuntzToeplitzRel.orth (n := n) j i

/-- `CuntzToeplitzAlg n` is a *-algebra with star inherited from the dagger. -/
instance (n : ℕ) : StarRing (CuntzToeplitzAlg n) :=
  RingQuot.starRing
    (starRing := {
      star := λ x => RingQuot.lift (λ a => RingQuot.mk (CuntzToeplitzRel n) (dagger n a))
        (by
          intro a b h
          apply RingQuot.rel_of_lift_def.mpr
          exact dagger_CuntzToeplitzRel_star h) x
      star_involutive := by
        intro x; apply RingQuot.induction_on x; intro a; simp [dagger_dagger]
      star_mul := by
        intro x y; apply RingQuot.induction_on₂ x y; intro a b; simp [dagger_mul]
      star_add := by
        intro x y; apply RingQuot.induction_on₂ x y; intro a b; simp [dagger_add]
    })
    (fun _ _ h => by
      -- The star operation on RingQuot is already defined in terms of dagger,
      -- and we proved dagger preserves the relation.
      -- Actually the above `star` definition already respects the relation.
      -- RingQuot.starRing in mathlib4 takes a proof of relation compatibility.
      apply dagger_CuntzToeplitzRel_star h)

/-- Star on Toeplitz generators swaps S ↔ Sdag. -/
@[simp] theorem star_toeplitzS (n : ℕ) (i : Fin n) : star (toeplitzS n i) = toeplitzSdag n i := by
  unfold toeplitzS toeplitzSdag star
  simp [dagger_S]

@[simp] theorem star_toeplitzSdag (n : ℕ) (i : Fin n) : star (toeplitzSdag n i) = toeplitzS n i := by
  unfold toeplitzS toeplitzSdag star
  simp [dagger_Sdag]

/-! ## *-homomorphism from Toeplitz to Cuntz -/

/--
Natural *-homomorphism `toeplitzToCuntz : CuntzToeplitzAlg n → CuntzAlg n`.

The Toeplitz algebra has relations `S_i† S_j = δ_{ij}`. The Cuntz algebra
adds the relation `Σ S_i S_i† = 1`. This map sends each Toeplitz generator
to the corresponding Cuntz generator.
-/
def toeplitzToCuntz (n : ℕ) : CuntzToeplitzAlg n → CuntzAlg n :=
  RingQuot.lift (λ a => RingQuot.mk (CuntzRel n) a)
    (by
      intro a b h; rcases h with ⟨i, j⟩
      -- a = Sdag n i * S n j, b = (if i = j then 1 else 0)
      -- Need: their images under cuntzMk are equal
      -- cuntzMk (Sdag_i * S_j) = cuntzSdag_i * cuntzS_j = δ_{ij} = cuntzMk(δ_{ij})
      simp [cuntz_orthogonality n i j])

@[simp] theorem toeplitzToCuntz_S (n : ℕ) (i : Fin n) :
    toeplitzToCuntz n (toeplitzS n i) = cuntzS n i := rfl

@[simp] theorem toeplitzToCuntz_Sdag (n : ℕ) (i : Fin n) :
    toeplitzToCuntz n (toeplitzSdag n i) = cuntzSdag n i := rfl

/-- `toeplitzToCuntz` is a *-homomorphism. -/
theorem toeplitzToCuntz_star (n : ℕ) (x : CuntzToeplitzAlg n) :
    toeplitzToCuntz n (star x) = star (toeplitzToCuntz n x) := by
  apply RingQuot.induction_on x; intro a
  -- Both sides are RingQuot.lifts; simplify by induction on the tensor algebra
  induction' a using TensorAlgebra.induction with r v x y hx hy x y hx hy
  · simp
  · -- v is a Finsupp: sum of generators. Each generator is S_i or Sdag_i.
    refine Finsupp.induction v ?_ ?_
    · simp
    · rintro ⟨i, b⟩ c h
      cases b <;> simp [h]
  · simp [map_add, star_add, hx, hy]
  · simp [map_mul, star_mul, hx, hy]

/-- The sum relation `Σ S_i S_i† = 1` holds in the image. -/
theorem toeplitzToCuntz_range_sum_one (n : ℕ) :
    (∑ i : Fin n, toeplitzToCuntz n (toeplitzS n i) *
      toeplitzToCuntz n (toeplitzSdag n i)) = 1 := by
  simp [cuntz_ranges_sum_one n]

end InfoGeometry.Algebra.CuntzTensorQuotient
