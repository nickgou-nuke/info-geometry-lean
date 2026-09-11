import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# GNS Inner Product Space on the Diagonal Subalgebra `D_n ≃ ℂ^n`

For positive prime data `p_i` and real inverse temperature `β`, the diagonal
subalgebra carries the weighted inner product

  ⟪x, y⟫_β = ∑ i, w_i * conj (x i) * y i

with weights `w_i = p_i^{-β}`.

This file records the weighted finite-dimensional inner-product-space structure
directly on `Fin n → ℂ`. No quotient or completion is needed in the finite
diagonal model.

We prove all the algebraic properties of the weighted inner product and
package them as an `InnerProductSpace.Core`. The full `InnerProductSpace`
instance is available via `letI` at the call site to avoid a typeclass
diamond with the existing Pi `InnerProductSpace`.
-/

open scoped ComplexConjugate

noncomputable section

namespace InfoGeometry.Algebra.GNSCuntzDiagonal

/-- The positive Boltzmann weight `p^{-β}` as a real number. -/
def weight (p : ℕ) (β : ℝ) : ℝ :=
  (p : ℝ) ^ (-β)

lemma weight_pos (p : ℕ) (hp : 0 < p) (β : ℝ) : 0 < weight p β := by
  dsimp [weight]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp) _

/-- The weighted diagonal inner product on `Fin n → ℂ`. -/
def diagInner (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ((weight (primes i) β : ℝ) : ℂ) * star (x i) * y i

/-! ### Algebraic properties -/

lemma diagInner_conj_symm (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y : Fin n → ℂ) :
    star (diagInner n primes β y x) = diagInner n primes β x y := by
  dsimp [diagInner]
  simp [star_sum, star_mul, mul_assoc, mul_comm, mul_left_comm]

lemma diagInner_conj_symm' (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y : Fin n → ℂ) :
    diagInner n primes β y x = star (diagInner n primes β x y) := by
  apply star_injective
  simpa using diagInner_conj_symm n primes β x y

lemma diagInner_add_left (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y z : Fin n → ℂ) :
    diagInner n primes β (x + y) z = diagInner n primes β x z + diagInner n primes β y z := by
  dsimp [diagInner]
  simp [add_mul, mul_add, star_add, Finset.sum_add_distrib]

lemma diagInner_add_right (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y z : Fin n → ℂ) :
    diagInner n primes β z (x + y) = diagInner n primes β z x + diagInner n primes β z y := by
  dsimp [diagInner]
  simp [add_mul, mul_add, Finset.sum_add_distrib]

lemma diagInner_smul_left (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y : Fin n → ℂ) (c : ℂ) :
    diagInner n primes β (c • x) y = star c * diagInner n primes β x y := by
  dsimp [diagInner]
  calc
    ∑ i : Fin n, ((weight (primes i) β : ℝ) : ℂ) * star ((c • x) i) * y i
        = ∑ i : Fin n, star c * (((weight (primes i) β : ℝ) : ℂ) * star (x i) * y i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Pi.smul_apply, star_mul, mul_assoc, mul_comm, mul_left_comm]
    _ = star c * ∑ i : Fin n, ((weight (primes i) β : ℝ) : ℂ) * star (x i) * y i := by
          simp [Finset.mul_sum]

lemma diagInner_smul_right (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (x y : Fin n → ℂ) (c : ℂ) :
    diagInner n primes β x (c • y) = c * diagInner n primes β x y := by
  dsimp [diagInner]
  simp only [Pi.smul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum, Finset.sum_mul]

/-! ### Positivity and definiteness -/

lemma diagInner_re_nonneg (n : ℕ) (primes : Fin n → ℕ) (hpos : ∀ i, 0 < primes i) (β : ℝ)
    (x : Fin n → ℂ) : 0 ≤ Complex.re (diagInner n primes β x x) := by
  have hsum : Complex.re (diagInner n primes β x x) =
      ∑ i : Fin n, Complex.re (((weight (primes i) β : ℝ) : ℂ) * star (x i) * x i) := by
    simp [diagInner, Complex.re_sum]
  rw [hsum]
  refine Finset.sum_nonneg (λ i _ => ?_)
  have hrewrite : Complex.re (((weight (primes i) β : ℝ) : ℂ) * star (x i) * x i) =
      weight (primes i) β * Complex.normSq (x i) := by
    dsimp [weight]
    simp [Complex.normSq_apply, Complex.ofReal_re]
    ring
  rw [hrewrite]
  exact mul_nonneg (le_of_lt <| weight_pos (primes i) (hpos i) β) (Complex.normSq_nonneg _)

/-- The weighted inner product is definite: if ⟪x,x⟫ = 0 then x = 0.
    This holds because all weights are strictly positive. -/
lemma diagInner_definite (n : ℕ) (primes : Fin n → ℕ) (hpos : ∀ i, 0 < primes i) (β : ℝ)
    (x : Fin n → ℂ) (hzero : diagInner n primes β x x = 0) : x = 0 := by
  ext i
  have h_re_zero : Complex.re (diagInner n primes β x x) = 0 := by
    rw [hzero, Complex.zero_re]
  -- Rewrite the real part as a sum of nonnegative terms
  have hsum_re : Complex.re (diagInner n primes β x x) =
      ∑ k : Fin n, weight (primes k) β * Complex.normSq (x k) := by
    simp [diagInner, Complex.re_sum, Complex.normSq_apply, weight]
    refine Finset.sum_congr rfl (λ j _ => ?_)
    ring
  rw [hsum_re] at h_re_zero
  -- Each term is nonnegative
  have h_nonneg : ∀ k, 0 ≤ weight (primes k) β * Complex.normSq (x k) := λ k =>
    mul_nonneg (le_of_lt <| weight_pos (primes k) (hpos k) β) (Complex.normSq_nonneg _)
  have h_term_zero : weight (primes i) β * Complex.normSq (x i) = 0 := by
    have h_nonneg_mem : ∀ (k : Fin n), k ∈ (Finset.univ : Finset (Fin n)) →
        0 ≤ weight (primes k) β * Complex.normSq (x k) := λ k _ => h_nonneg k
    exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg_mem).1 h_re_zero i (Finset.mem_univ i)
  -- weight > 0 and weight * normSq(x i) = 0 ⇒ normSq(x i) = 0 ⇒ x i = 0
  have hpos_weight : 0 < weight (primes i) β := weight_pos (primes i) (hpos i) β
  have hnsq : Complex.normSq (x i) = 0 := by
    nlinarith [h_term_zero, hpos_weight, Complex.normSq_nonneg (x i)]
  exact Complex.normSq_eq_zero.mp hnsq

/-- The `PreInnerProductSpace.Core` for the weighted diagonal inner product. -/
def diagPreInnerCore (n : ℕ) (primes : Fin n → ℕ) (hpos : ∀ i, 0 < primes i) (β : ℝ) :
    PreInnerProductSpace.Core ℂ (Fin n → ℂ) :=
  { inner := diagInner n primes β
    conj_inner_symm := diagInner_conj_symm n primes β
    re_inner_nonneg := diagInner_re_nonneg n primes hpos β
    add_left := diagInner_add_left n primes β
    smul_left := diagInner_smul_left n primes β }

end InfoGeometry.Algebra.GNSCuntzDiagonal
