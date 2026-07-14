import Mathlib

/-!
# Asano-Ruelle unrestricted claim obstruction

This file proves that the unrestricted Asano-Ruelle source claim is false if
`K₁, K₂ : Set ℂ` are arbitrary.

Counterexample:

* `K₁ = Set.univ`,
* `K₂ = {0}`,
* `Φ(z₁,z₂) = 1 + z₁ z₂`,
* `Q(z) = 1 + z`.

The zero-freeness premise is vacuous because there is no `z₁ ∉ K₁`.
But `Q(-1)=0`, while `-1 ∉ -(K₁K₂) = {0}`.
-/

namespace AsanoRuelleObstruction

/-- Two-variable separately affine block. -/
def Phi (A B C D z₁ z₂ : ℂ) : ℂ :=
  A + B * z₁ + C * z₂ + D * z₁ * z₂

/-- Contracted one-variable polynomial. -/
def contractedQ (A D z : ℂ) : ℂ :=
  A + D * z

/-- Forbidden product set `-(K₁K₂)`. -/
def forbiddenProductSet (K₁ K₂ : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ u ∈ K₁, ∃ v ∈ K₂, z = -(u * v)}

/--
The unrestricted Asano-Ruelle source claim is false.
-/
theorem asanoRuelle_unrestricted_claim_false :
    ¬
      (∀ (A B C D : ℂ) (K₁ K₂ : Set ℂ),
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          Phi A B C D z₁ z₂ ≠ 0) →
        ∀ z : ℂ,
          z ∉ forbiddenProductSet K₁ K₂ →
          contractedQ A D z ≠ 0) := by
  intro hClaim

  let K₁ : Set ℂ := Set.univ
  let K₂ : Set ℂ := {0}

  have hZeroFree :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        Phi 1 0 0 1 z₁ z₂ ≠ 0 := by
    intro z₁ z₂ hz₁ _hz₂
    exact False.elim (hz₁ (Set.mem_univ z₁))

  have hConclusion :=
    hClaim 1 0 0 1 K₁ K₂ hZeroFree (-1)

  have hNotForbidden :
      (-1 : ℂ) ∉ forbiddenProductSet K₁ K₂ := by
    rintro ⟨u, _hu, v, hv, hEq⟩
    have hv0 : v = 0 := by
      simpa [K₂] using hv
    rw [hv0, mul_zero, neg_zero] at hEq
    norm_num at hEq

  have hRoot :
      contractedQ 1 1 (-1 : ℂ) = 0 := by
    norm_num [contractedQ]

  exact hConclusion hNotForbidden hRoot

end AsanoRuelleObstruction

