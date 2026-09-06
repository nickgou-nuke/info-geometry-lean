import Mathlib.Tactic

open Set
open scoped ComplexOrder

namespace InfoGeometry.AsanoRuelle

/-- Forbidden product set `-(K₁ K₂)`. -/
def negProductSet (K₁ K₂ : Set ℂ) : Set ℂ :=
  { z : ℂ | ∃ u ∈ K₁, ∃ v ∈ K₂, z = -(u * v) }

/--
The unrestricted two-variable Asano contraction statement is false.

Counterexample:

* `K₁ = univ`
* `K₂ = {0}`
* `Φ(z₁,z₂) = -1 + z₁ z₂`
* `Q(z) = -1 + z`

The zero-free premise is vacuous because there is no `z₁ ∉ K₁`.
But `Q(1)=0`, while `1 ∉ -(K₁K₂) = {0}`.
-/
theorem unrestricted_asano_contraction_statement_false :
    ¬
      (∀ (A B C D : ℂ) (K₁ K₂ : Set ℂ),
        (∀ z₁ : ℂ, z₁ ∉ K₁ →
          ∀ z₂ : ℂ, z₂ ∉ K₂ →
            A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0) →
        ∀ z : ℂ,
          z ∉ negProductSet K₁ K₂ →
            A + D * z ≠ 0) := by
  intro h

  let A : ℂ := -1
  let B : ℂ := 0
  let C : ℂ := 0
  let D : ℂ := 1
  let K₁ : Set ℂ := Set.univ
  let K₂ : Set ℂ := {0}

  have hzeroFree :
      ∀ z₁ : ℂ, z₁ ∉ K₁ →
        ∀ z₂ : ℂ, z₂ ∉ K₂ →
          A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0 := by
    intro z₁ hz₁
    exact False.elim (hz₁ (Set.mem_univ z₁))

  have hone_not_in_product :
      (1 : ℂ) ∉ negProductSet K₁ K₂ := by
    intro hmem
    rcases hmem with ⟨u, hu, v, hv, hvprod⟩
    have hv0 : v = 0 := by
      simpa [K₂] using hv
    have hbad : (1 : ℂ) = 0 := by
      have htmp := hvprod
      simp [hv0] at htmp
    exact one_ne_zero hbad

  have hQ_nonzero :
      A + D * (1 : ℂ) ≠ 0 :=
    h A B C D K₁ K₂ hzeroFree 1 hone_not_in_product

  have hQ_zero : A + D * (1 : ℂ) = 0 := by
    norm_num [A, D]

  exact hQ_nonzero hQ_zero

end InfoGeometry.AsanoRuelle
