import Mathlib.Tactic

namespace Omega.POM.OrbitProductNorm

open Finset

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Off-diagonal pairs of a finite type `n`.
    rem:pom-a4-u4-orbit-product-norm -/
def offDiagonalPairs (n : Type*) [Fintype n] [DecidableEq n] : Finset (n × n) :=
  (Finset.univ : Finset (n × n)).filter (fun p => p.1 ≠ p.2)

@[simp] theorem mem_offDiagonalPairs {p : n × n} :
    p ∈ offDiagonalPairs n ↔ p.1 ≠ p.2 := by
  unfold offDiagonalPairs
  simp

/-- Cardinality of `univ.erase i`: `|n| - 1`.
    rem:pom-a4-u4-orbit-product-norm -/
theorem card_erase_univ (i : n) :
    ((Finset.univ : Finset n).erase i).card = Fintype.card n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  rfl

/-- Product over off-diagonal pairs split by first coordinate.
    rem:pom-a4-u4-orbit-product-norm -/
theorem prod_offDiag_by_fst (f : n × n → K) :
    ∏ p ∈ offDiagonalPairs n, f p =
      ∏ i : n, ∏ j ∈ (Finset.univ : Finset n).erase i, f (i, j) := by
  exact Finset.prod_finset_product (r := offDiagonalPairs n)
    (s := (Finset.univ : Finset n))
    (t := fun i => (Finset.univ : Finset n).erase i)
    (f := f) (by
      intro p
      simp [offDiagonalPairs, ne_comm])

/-- Product over off-diagonal pairs split by second coordinate.
    rem:pom-a4-u4-orbit-product-norm -/
theorem prod_offDiag_by_snd (f : n × n → K) :
    ∏ p ∈ offDiagonalPairs n, f p =
      ∏ j : n, ∏ i ∈ (Finset.univ : Finset n).erase j, f (i, j) := by
  calc
    ∏ p ∈ offDiagonalPairs n, f p =
        ∏ p ∈ offDiagonalPairs n, f (p.2, p.1) := by
      apply Finset.prod_equiv (Equiv.prodComm n n)
      · intro p
        simp [offDiagonalPairs, ne_comm]
      · intro p hp
        rfl
    _ = ∏ j : n, ∏ i ∈ (Finset.univ : Finset n).erase j, f (i, j) :=
      Finset.prod_finset_product (r := offDiagonalPairs n)
        (s := (Finset.univ : Finset n))
        (t := fun j => (Finset.univ : Finset n).erase j)
        (f := fun p => f (p.2, p.1)) (by
          intro p
          simp [offDiagonalPairs, ne_comm])

/-- Numerator product: `∏_{i≠j} (α i)² = ∏_i (α i)^(2(|n|-1))`.
    rem:pom-a4-u4-orbit-product-norm -/
theorem prod_numerator (α : n → K) :
    ∏ p ∈ offDiagonalPairs n, (α p.1)^2 =
      ∏ i : n, (α i)^(2 * (Fintype.card n - 1)) := by
  rw [prod_offDiag_by_fst]
  apply Finset.prod_congr rfl
  intro i _
  show ∏ _j ∈ (Finset.univ : Finset n).erase i, (α i)^2 =
      (α i)^(2 * (Fintype.card n - 1))
  rw [Finset.prod_const, card_erase_univ, ← pow_mul]

/-- Denominator product: `∏_{i≠j} α j = ∏_j (α j)^(|n|-1)`.
    rem:pom-a4-u4-orbit-product-norm -/
theorem prod_denominator (α : n → K) :
    ∏ p ∈ offDiagonalPairs n, α p.2 =
      ∏ j : n, (α j)^(Fintype.card n - 1) := by
  rw [prod_offDiag_by_snd]
  apply Finset.prod_congr rfl
  intro j _
  show ∏ _i ∈ (Finset.univ : Finset n).erase j, α j =
      (α j)^(Fintype.card n - 1)
  rw [Finset.prod_const, card_erase_univ]

/-- Orbit product identity (core).
    rem:pom-a4-u4-orbit-product-norm -/
theorem orbit_product_identity (α : n → K) (hα : ∀ i, α i ≠ 0) :
    ∏ p ∈ offDiagonalPairs n, (α p.1)^2 / (α p.2) =
      (∏ k : n, α k)^(Fintype.card n - 1) := by
  rw [Finset.prod_div_distrib]
  rw [prod_numerator, prod_denominator]
  set N := Fintype.card n
  have hprod_ne : (∏ j : n, (α j)^(N - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hα i))
  rw [div_eq_iff hprod_ne]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add]
  congr 1
  omega

/-- Concrete `n = Fin 5` instance: exponent = 4.
    rem:pom-a4-u4-orbit-product-norm -/
theorem orbit_product_n5 (α : Fin 5 → K) (hα : ∀ i, α i ≠ 0) :
    ∏ p ∈ offDiagonalPairs (Fin 5), (α p.1)^2 / (α p.2) =
      (∏ k : Fin 5, α k)^4 := by
  have h := orbit_product_identity α hα
  simpa [Fintype.card_fin] using h

/-- Paper wrapper: A₄ × U₄ orbit product norm identity.
    rem:pom-a4-u4-orbit-product-norm -/
theorem paper_pom_a4_u4_orbit_product_norm (α : n → K) (hα : ∀ i, α i ≠ 0) :
    ∏ p ∈ offDiagonalPairs n, (α p.1)^2 / (α p.2) =
      (∏ k : n, α k)^(Fintype.card n - 1) :=
  orbit_product_identity α hα

end Omega.POM.OrbitProductNorm
